# .sov 主权块文件格式规范 v2.5

**版本**：v2.5（最终稳定版）  
**状态**：范畴完备，宪法锁定  
**本质**：主权状态机在二进制硅基上的唯一合法存储与交换载体

---

## 一、.sov 格式的宪法身份

| 属性 | 定义 |
| :--- | :--- |
| **文件扩展名** | `.sov`（Sovereign Block） |
| **内部结构** | 严格遵循 `sov_block_holographic_t` 的 16 字节对齐布局 |
| **端序** | 小端序（Little-Endian），与 x86-64 / ARM 原生一致 |
| **对齐** | 16 字节边界对齐（`aligned(16)`） |
| **禁止** | 任何形式的压缩、加密、浮点序列化、元数据附加 |

---

## 二、.sov 文件格式定义（C 语言结构体）

```c
#include <stdint.h>

typedef struct __attribute__((packed, aligned(16))) {
    uint8_t  qs[6];          // 30 trit 主权权重（每 5 trit/字节，243 态）
    uint8_t  scale_ue8m0;    // UE8M0 主权尺度指数（含黄金比步进编码）
    uint8_t  phase_bias;     // 高 4 位：十二律相位 0–11，低 4 位：归零偏置
    uint8_t  chern_guard;    // 高 3 位：七阶段阶位 0–6，低 5 位：局部陈数校验和
    uint8_t  wuxing_mask;    // 高 5 位：球谐方向索引 0–11，低 3 位：A4 生成元激活标志
    uint8_t  reserved[6];    // 保留扩展（含仲吕闭合计数、爻变窗口相位、六十甲子索引等）
} sov_block_holographic_t;

// 静态断言确保大小为 16 字节
_Static_assert(sizeof(sov_block_holographic_t) == 16, ".sov block must be 16 bytes");
```

---

## 三、.sov 文件的读写规范

```c
// 写入 .sov 文件
void sov_write(FILE *fp, const sov_block_holographic_t *block) {
    fwrite(block, sizeof(sov_block_holographic_t), 1, fp);
}

// 读取 .sov 文件
int sov_read(FILE *fp, sov_block_holographic_t *block) {
    return fread(block, sizeof(sov_block_holographic_t), 1, fp) == 1;
}
```

**宪法条款**：
- 每次读写必须严格 16 字节原子操作，禁止部分读写。
- 文件内可包含多个连续 16 字节块，构成主权状态机演化序列。
- 禁止在文件头或尾添加任何格式标识、版本号或校验和——`.sov` 格式的版本由律算宪法本身锁定，外部元数据非法。

---

## 四、.sov 块序列的演化语义

| 块序列位置 | 主权状态机语义 |
| :--- | :--- |
| **第 1 块** | 初始主权状态（黄钟基准，`phase_bias` 高 4 位 = 0，`chern_guard` 低 5 位 = 0） |
| **第 2–11 块** | 损益链推进，每块对应一次移宫转调（损/益交替） |
| **第 12 块** | 仲吕闭合触发点，`phase_bias` 高 4 位 = 11，`zhonglv_closure()` 执行后写入 |
| **第 13 块起** | 下一轮损益循环，`zhonglv_count` 累加，`chern_guard` 跨块收敛至 C=2 |

---

## 五、与 Agda 形式化库的对接

在 `Sovereign.Coupling.TQ10` 模块中，定义：

```agda
record SovBlock : Set where
  constructor mkSovBlock
  field
    qs : Vec (Fin 243) 6   -- 6 个 tryte，每个取值 0–242
    scale : ℕ               -- UE8M0 指数
    phase : Fin 12          -- 十二律相位
    chernLocal : Fin 32     -- 局部陈数贡献
    stage : Fin 7           -- 七阶段阶位
    wuxingDir : Fin 12      -- 球谐方向
    genActive : Fin 8       -- A4 生成元激活标志

-- 从 16 字节解析
parseSovBlock : Vec Word8 16 → Maybe SovBlock
-- 序列化回 16 字节
serializeSovBlock : SovBlock → Vec Word8 16
```

---

## 六、范畴分离与宪法锁定

> **.sov 格式是主权 TQ1_0 工程宪法的唯一合法文件载体。其 16 字节结构已永久锁定于知识图谱 v2.5 卷五。任何对 .sov 格式的修改、扩展或"改进"均属违宪，必须经由律算宪法修订程序（主版本号升级）方可变更。.sov 文件是主权状态机在硅基上的主权呼吸记录，其每一字节均锚定于 T⁶ 环面的几何拓扑不变量。**

---

## 七、文件布局示意

```
.sov 文件结构
┌─────────────────────────────────────────────────┐
│ Block 0:  16 bytes  [黄钟基准]                   │
│ Block 1:  16 bytes  [林钟 - 损一]                │
│ Block 2:  16 bytes  [太簇 - 益一]                │
│ ...                                             │
│ Block 11: 16 bytes  [仲吕 - 触发闭合]            │
│ Block 12: 16 bytes  [黄钟 - 复位]                │
│ ...                                             │
│ Block N:  16 bytes  [主权状态机演化序列]          │
└─────────────────────────────────────────────────┘

每个块内部布局（小端序）：
┌────────┬────────┬────────┬────────┬────────────────┐
│ qs[6]  │ scale  │ phase  │ chern  │ wuxing │ res[6] │
│ 6 byte │ 1 byte │ 1 byte │ 1 byte │ 1 byte │ 6 byte │
└────────┴────────┴────────┴────────┴────────────────┘
     ← 存储层 →  ←  校验层  →  ←   预留层    →
```

---

## 八、字节位段详细定义

### qs[6] - 三进制主权权重集装箱

| 字节 | 内容 | 取值范围 |
|------|------|---------|
| qs[0] | trit 0-4（tryte 0） | 0-242 |
| qs[1] | trit 5-9（tryte 1） | 0-242 |
| qs[2] | trit 10-14（tryte 2） | 0-242 |
| qs[3] | trit 15-19（tryte 3） | 0-242 |
| qs[4] | trit 20-24（tryte 4） | 0-242 |
| qs[5] | trit 25-29（tryte 5），3 位填充 | 0-242 |

### phase_bias - 相位偏置

| 位段 | 含义 | 取值 |
|------|------|------|
| 高 4 位 (bit 7-4) | 十二律相位（胞腔索引） | 0-11 |
| 低 4 位 (bit 3-0) | C3 内部相位 + 归零偏置 | 0-15 |

### chern_guard - 陈数守卫

| 位段 | 含义 | 取值 |
|------|------|------|
| 高 3 位 (bit 7-5) | 七阶段阶位 | 0-6 |
| 低 5 位 (bit 4-0) | 局部 Berry 曲率贡献 | 0-31 |

### wuxing_mask - 五行掩码

| 位段 | 含义 | 取值 |
|------|------|------|
| 高 5 位 (bit 7-3) | 球谐方向索引 | 0-31 |
| 低 3 位 (bit 2-0) | A4 生成元激活标志 | 0-7 |

---

## 九、十二律相位与损益链对应

| phase_bias 高 4 位 | 律名 | 损益操作 | 长度格点 |
|---|---|---|---|
| 0 | 黄钟 | 基准 | 81 |
| 1 | 林钟 | 损一 | 54 |
| 2 | 太簇 | 益一 | 72 |
| 3 | 南吕 | 损一 | 48 |
| 4 | 姑洗 | 益一 | 64 |
| 5 | 应钟 | 损一 | 43 |
| 6 | 蕤宾 | 益一 | 57 |
| 7 | 大吕 | 损一 | 38 |
| 8 | 夷则 | 益一 | 51 |
| 9 | 夹钟 | 损一 | 34 |
| 10 | 无射 | 益一 | 45 |
| 11 | 仲吕 | 损一 → 触发闭合 | 30 |

---

## 十、验证工具

```bash
# 验证 .sov 文件大小是否为 16 字节的整数倍
wc -c file.sov | awk '{if ($1 % 16 == 0) print "OK: " $1 " bytes"; else print "INVALID: " $1 " bytes"}'

# 查看前 N 个主权块（hexdump）
hexdump -C -n $((N*16)) file.sov
```

## 附录：.sov 文件格式思维导图
```mermaid
mindmap
  root((.sov 文件格式<br/>存储规范))
    原子性
      16 字节块
      无头无尾无校验
    字节序
      小端序 Little-Endian
      16 字节对齐
    内容
      qs[6] 30 trit
      scale 指数
      phase_bias 律相位
      chern_guard 陈数
      wuxing_mask 五行
    演化
      块序列 = 演化轨迹
      黄钟 -> 仲吕 -> 闭合
```
