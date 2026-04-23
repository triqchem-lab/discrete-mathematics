# vlut.cpp 深度源码分析与律算工程借鉴

**版本**：v2.5  
**分析日期**：2025  
**vlut.cpp 版本**：基于 llama.cpp 的 VLUT 扩展 (arXiv: 2512.06443)

---

## 一、vlut.cpp 核心架构

### 1.1 项目定位

**vlut.cpp** 是基于查找表 (LUT) 的 1.58-bit 三进制 LLM 推理引擎，核心创新：
- 用 LUT 替代反量化 + 乘法
- 向量 LUT 范式：1→N 查找 + 连续向量加法
- Cache 友好的流式查找模式

### 1.2 核心源码结构

```
vlut.cpp/
├── ggml/src/
│   ├── ggml-quants-vlut.c/h      # 三进重量化处理 (178 行)
│   └── ggml-cpu/
│       └── ggml-cpu-quants-vlut.c # VLUT GEMM 内核 (2210 行)
├── convert_hf_to_gguf_vlut.py     # 模型转换工具
└── evaluation/                    # 评估管线
```

---

## 二、三进重量化实现深度分析

### 2.1 三进制编码逻辑 (ggml-quants-vlut.c)

```c
// 核心编码: 浮点 → 三进制 {-1, 0, 1} → 打包为字节
size_t quantize_i1_v(const float *src, void *dst, ...) {
    // 1. 三进制映射
    uint8_t tmp = 1;  // 默认 0 (平衡态)
    if (fabs(v) > eps) {
        tmp = v > 0. ? 2 : 0;  // +1 → 2, -1 → 0
    }
    
    // 2. 5 trit 打包为 1 字节 (3^5 = 243 态)
    w = w * 3 + tmp;  // 基数 3 累加
}
```

**关键发现**：
- **映射规则**: `{-1, 0, 1} → {0, 1, 2}` (与律算完全一致)
- **打包方式**: 每 5 个 trit 打包为 1 字节 (243 态)
- **剩余空间**: 256 - 243 = 13 态未使用 (可作特殊标记)

**与律算 PackedTryte5 的对应关系**：

| 概念 | vlut.cpp | 律算 Sovereign Core |
|------|----------|-------------------|
| 三进制映射 | `v > 0 ? 2 : (fabs(v)>eps ? 0 : 1)` | `Trit.T2/T1/T0` |
| 打包基数 | 5 trit/字节 (243 态) | `PackedTryte5` (243 态) |
| 剩余态 | 13 态未使用 | 13 态能隙奇点捕获区 |
| 编码验证 | ✅ 完全一致 | ✅ 完全一致 |

### 2.2 I2_V 量化 (2-bit, 4 trit/字节)

```c
size_t quantize_i2_v(const float *src, void *dst, ...) {
    // 4 trit 打包: 3^4 = 81 态 < 256
    for (int k = 3; k >= 0; k--) {
        w = w * 3 + tmp;  // 基数 3 累加
    }
}
```

**律算借鉴**：律算可同时支持 I1_V (5 trit) 和 I2_V (4 trit) 两种打包模式。

---

## 三、VLUT GEMM 内核深度分析

### 3.1 核心算法：查找表替代乘法

**传统矩阵乘法**：`C[i,j] = Σ_k A[i,k] * B[k,j]` (需要 N³ 次乘法)

**VLUT 方法**：
1. **预计算查找表**：对每个唯一的 B[k,j] 值，预先计算 `table[v] = v * B[k,j]`
2. **查找替代乘法**：`C[i,j] = Σ_k table[A[i,k]]` (只需 N³ 次查找 + 加法)

### 3.2 核心宏定义分析

```c
// 1. 查找表构建 (以 I1_V 为例)
#define MAKE_TABLES_I1_58S_BLOCK4(g) \
    gemm_make_table_i1v(table0, y_block + (((g)*group_size + (i * tile_size + 0) * 5) * TABLE_ENTRY_SIZE));
    // ... 4 个表同时构建

// 2. 查找 + 向量加法 (核心加速点)
#define ADD_TABLE_ENTRIES_BLOCK4(nc) \
    for (int c = 0; c < (nc); c++) {
        uint8_t v0 = x_block[c * tile_size + 0];  // 1. 获取索引
        const int16_t *rt0 = table0 + v0 * TABLE_ENTRY_SIZE;  // 2. 查找
        int16_t *rs = sum_i16 + c * TABLE_ENTRY_SIZE;
        for (int r = 0; r < TABLE_ENTRY_SIZE; r++) {
            rs[r] += rt0[r];  // 3. 向量加法替代乘法
        }
    }
```

**性能关键**：
- 查找表大小：243 × TABLE_ENTRY_SIZE × sizeof(int16_t)
- 向量化：使用 AVX512/SVE/NEON 加速向量加法
- Cache 友好：连续内存访问模式

### 3.3 I1_V GEMM 完整流程

```c
void ggml_gemm_i1v_i8v_lut(...) {
    // 1. 分配缓冲区
    int16_t *sum_i16 = malloc(sizeof(int16_t) * TABLE_ENTRY_SIZE * nc);
    int32_t *sum_i32 = malloc(sizeof(int32_t) * nr * nc);
    int16_t *table = malloc(sizeof(int16_t) * TABLE_ENTRY_SIZE * 243);
    
    // 2. 分块处理 (group_size = 640)
    // 每个块包含 640 个权重，按 5 trit 分组
    
    // 3. 对每个输出列:
    for (每个块) {
        // 3a. 构建查找表 (81 表 × 243 项)
        MAKE_TABLES_I1_58S_BLOCK4(group);
        
        // 3b. 查找 + 累加
        ADD_TABLE_ENTRIES_BLOCK4(nc);
        
        // 3c. 转置累积结果
        ACCUMULATE_TABLE_TRANS(sum_i16, sum_i32, ...);
    }
    
    // 4. 应用缩放因子
    for (r = 0; r < nr; r++) {
        for (c = 0; c < nc; c++) {
            s[r][c] = sum_i32[r][c] * scale[r];
        }
    }
}
```

### 3.4 SIMD 向量化优化

```c
// AVX512 版本 (x86)
#if defined(VLUT_AVX512)
    #define ADD_TABLE_ENTRIES(rs, rt, size) \
    do {
        __m512i rs_vec = _mm512_loadu_si512((rs));  // 加载 32 个 int16
        __m512i rt_vec = _mm512_loadu_si512((rt));
        rs_vec = _mm512_add_epi16(rs_vec, rt_vec);  // 向量加法
        _mm512_storeu_si512((rs), rs_vec);
    } while(0)

// ARM SVE 版本
#elif defined(VLUT_SVE)
    #define ADD_TABLE_ENTRIES(rs, rt, size) \
    do {
        svint16_t acc = svld1_s16(pg, (rs));  // SVE 加载
        svint16_t tab = svld1_s16(pg, (rt));
        acc = svadd_s16_z(pg, acc, tab);      // SVE 向量加法
        svst1_s16(pg, (rs), acc);             // SVE 存储
    } while(0)
```

**律算借鉴**：主权状态机的五行干涉运算可使用相同的 SIMD 优化策略。

---

## 四、对律算合一工程实践的核心借鉴

### 4.1 直接可复用的算法

#### 4.1.1 三进制打包/解包

```python
# 律算可完全复用 vlut.cpp 的打包逻辑
def quantize_i1_v(weights: List[float]) -> List[int]:
    """三进重量化 (与 vlut.cpp 完全等价)"""
    eps = 1e-6
    packed = []
    
    # 按 5 trit 一组打包
    for i in range(0, len(weights), 5):
        w = 0
        for k in range(4, -1, -1):  # 从高到低
            v = weights[i + k] if (i + k) < len(weights) else 0.0
            if abs(v) > eps:
                tmp = 2 if v > 0 else 0
            else:
                tmp = 1
            w = w * 3 + tmp
        packed.append(w)
    
    return packed
```

#### 4.1.2 查找表构建

```python
def gemm_make_table_i1v(table: np.ndarray, y_block: np.ndarray):
    """构建 I1_V 查找表 (参考 vlut.cpp)"""
    # table[v] = v * y_block 的预计算
    # v ∈ {0, 1, 2} 对应 {-1, 0, 1}
    for v in range(243):
        # 解码 5 trit
        trits = decode_5_trit(v)
        # 计算 trit 与 y_block 的点积
        table[v] = np.dot(trits, y_block)
```

#### 4.1.3 向量化查找累加

```python
def add_table_entries_vectorized(rs: np.ndarray, rt: np.ndarray):
    """向量化查找累加 (参考 vlut.cpp ADD_TABLE_ENTRIES)"""
    # 使用 numpy 的向量化操作
    rs += rt  # 等价于 vlut.cpp 的 SIMD 向量加法
```

### 4.2 架构设计借鉴

#### 4.2.1 分块策略

```
vlut.cpp 分块:
├── group_size = 640 (每组 640 个权重)
├── tile_size = 16 (每次处理 16 个输出)
└── block_size = 4/8/16/32 (SIMD 并行度)

律算可借鉴:
├── group_size = 640 → 128 个 5-trit 打包
├── tile_size = 16 → 16 个五行同时计算
└── block_size = 5 trit → PackedTryte5 自然对齐
```

#### 4.2.2 内存布局优化

```c
// vlut.cpp 的 Cache 友好布局
vx (输入): [group][5-trit-packed]  → 连续访问
vy (权重): [entry][TABLE_ENTRY_SIZE] → 表项连续
sum_i16:   [column][TABLE_ENTRY_SIZE] → 累加器连续

// 律算 TQ1_0 可借鉴:
qs[6] 布局: [Tryte0][Tryte1]...[Tryte4] → 五行连续
reserved: 对齐到 16 字节边界
```

### 4.3 性能优化借鉴

#### 4.3.1 查找表大小优化

```
vlut.cpp:
├── I1_V: 243 表项 × 16 输出 = 3888 int16 = 7.6 KB
├── I2_V: 81 表项 × 16 输出 = 1296 int16 = 2.5 KB
└── 总计: ~10 KB / 线程 (适合 L1 Cache)

律算可设置:
├── 主权 LUT: 243 × 16 × sizeof(int16) = 7.6 KB
├── 五行 LUT: 5 × 243 × sizeof(int16) = 2.4 KB
└── 总计: ~10 KB / 主权状态机
```

#### 4.3.2 启发式分块

```c
// vlut.cpp 无需调优的分块参数
static const int group_size = 640;  // 固定值

// 律算可设置固定参数:
const int SOVEREIGN_GROUP_SIZE = 640;  // 与 vlut.cpp 对齐
const int WUXING_TILE_SIZE = 5;        // 五行自然对齐
```

---

## 五、vlut.cpp 与律算的范畴映射

| vlut.cpp 概念 | 律算对应 | 范畴 |
|--------------|---------|------|
| 三进制权重 | Trit {-1, 0, 1} | 根数学 |
| 5 trit 打包 | PackedTryte5 | 耦合域 |
| 查找表 | VLUT ROM | 工程实现 |
| 向量加法 | 五行干涉累加 | 耦合域 |
| 分块策略 | 十二律分段 | 结构学 |
| SIMD 优化 | V-AVX3 指令集 | 硬件加速 |
| group_size=640 | 主权分组大小 | 工程规范 |
| TABLE_ENTRY_SIZE | 陈数校验窗口 | 耦合域 |

---

## 六、律算工程实现路线图 (借鉴 vlut.cpp)

### 阶段 1: 核心库完善 (当前已完成)
- ✅ Trit/Tryte/PackedTryte5 类型定义
- ✅ 损益操作/仲吕闭合
- ✅ TQ1_0 格式序列化

### 阶段 2: VLUT 内核实现 (下一步)
- [ ] 实现 `sovereign_lut_kernel()` (参考 `ggml_gemm_i1v_i8v_lut`)
- [ ] 243 项查找表预计算
- [ ] SIMD 向量化累加 (AVX2/NEON)

### 阶段 3: 格式转换工具
- [ ] `convert_agda_to_sovereign.py` (参考 `convert_hf_to_gguf_vlut.py`)
- [ ] Agda 规范 → Python 核心库 → VLUT 量化

### 阶段 4: 硬件部署
- [ ] FPGA VLUT ROM 设计 (参考 vlut.cpp AVX512 实现)
- [ ] 仲吕闭合硬件单元
- [ ] 陈数校验单元

---

## 七、关键发现总结

### 7.1 律算设计正确性验证

| 律算设计 | vlut.cpp 验证 | 状态 |
|---------|--------------|------|
| 5 trit 打包 (243 态) | 完全一致 | ✅ 验证通过 |
| 13 态剩余空间 | 未使用 (可作为奇点捕获区) | ✅ 兼容 |
| 三进制映射 {-1,0,1}→{0,1,2} | 完全一致 | ✅ 验证通过 |
| LUT 替代乘法 | 核心加速机制 | ✅ 验证通过 |

### 7.2 可直接复用的代码

1. **三进重量化逻辑** (`quantize_i1_v`) → 律算 `sovereign_quantize()`
2. **查找表构建** (`gemm_make_table_i1v`) → 律算 `make_sovereign_lut()`
3. **向量累加宏** (`ADD_TABLE_ENTRIES`) → 律算 `accumulate_wuxing()`
4. **分块策略** (group_size=640) → 律算主权分组大小

### 7.3 性能预期

基于 vlut.cpp 的论文数据：
- **VLUT vs 反量化+乘法**: 2-3 倍加速
- **AVX512 vs 标量**: 8-16 倍加速
- **律算预期**: 使用相同优化策略，主权状态机演化速度可提升 10 倍以上

---

## 八、结论

**vlut.cpp 是律算合一工程实现的最佳参考实现**，其核心算法与律算宪法设计高度一致：
1. 三进制编码逻辑完全匹配
2. 5 trit 打包方案可直接复用
3. VLUT 内核可作为主权状态机加速基础
4. SIMD 优化策略可直接移植

**建议下一步**：
1. 基于 vlut.cpp 的 `ggml_gemm_i1v_i8v_lut` 实现主权 VLUT 内核
2. 复用其三进重量化逻辑建立转换管线
3. 借鉴其 SIMD 优化策略实现 V-AVX3 指令集
