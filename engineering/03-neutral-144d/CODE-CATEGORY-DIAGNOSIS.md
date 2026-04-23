# 代码实现范畴偏离诊断报告 v2.5

**版本**：v2.5-诊断  
**状态**：诊断完成，待修正  
**日期**：2025

---

## 一、诊断结果总览

| 模块 | 文件 | 范畴正确性 | 问题 | 严重程度 |
|------|------|-----------|------|---------|
| **trit.py** | 根数学 | ⚠️ 部分偏离 | GF(3) 加法降维为模 3 算术 | 中 |
| **tryte.py** | 结构学/耦合域 | ✅ 基本正确 | 无重大问题 | 无 |
| **loss_gain.py** | 耦合域 | ⚠️ 部分降维 | 使用 Python 整数除法，非 LCM 模环 | 高 |
| **tq10_format.py** | 耦合域 | ⚠️ 部分降维 | qs 存储为字节列表，未体现 Tryte 拓扑 | 中 |
| **wuxing.py** | 元结构层 | ✅ 基本正确 | 无重大问题 | 无 |

---

## 二、详细诊断

### 2.1 trit.py (根数学) - ⚠️ 部分偏离

#### 问题 1: GF(3) 加法降维

```python
# 当前实现 (降维):
def gf3_add(a: Trit, b: Trit) -> Trit:
    result = (a.value + b.value) % 3  # 降维为模 3 算术
    if result == 0:
        return Trit.T1
    elif result == 1:
        return Trit.T2
    else:
        return Trit.T0
```

**问题**：将 GF(3) 降维为普通模 3 算术，丢失了三进制的驻波拓扑意义。

**正确实现**：GF(3) 加法应体现驻波三态的叠加/相消：

```python
# 正确实现 (拓扑):
def gf3_add(a: Trit, b: Trit) -> Trit:
    """
    GF(3) 驻波叠加:
    T₀(-1) + T₂(+1) = T₁(0)  ← 虚实对消灭
    T₀(-1) + T₀(-1) = T₂(+1) ← 吸收叠加为表达
    T₂(+1) + T₂(+1) = T₀(-1) ← 表达叠加为吸收
    T₁(0)  + x      = x       ← 平衡态为单位元
    """
    add_table = {
        (Trit.T0, Trit.T0): Trit.T2,  # -1 + -1 = +1 (mod 3)
        (Trit.T0, Trit.T1): Trit.T0,
        (Trit.T0, Trit.T2): Trit.T1,  # -1 + +1 = 0  (虚实对消灭)
        (Trit.T1, Trit.T0): Trit.T0,
        (Trit.T1, Trit.T1): Trit.T1,
        (Trit.T1, Trit.T2): Trit.T2,
        (Trit.T2, Trit.T0): Trit.T1,  # +1 + -1 = 0  (虚实对消灭)
        (Trit.T2, Trit.T1): Trit.T2,
        (Trit.T2, Trit.T2): Trit.T0,  # +1 + +1 = -1 (mod 3)
    }
    return add_table[(a, b)]
```

---

### 2.2 loss_gain.py (耦合域) - ⚠️ 高严重性

#### 问题 1: 使用 Python 整数除法 (降维)

```python
# 当前实现 (降维):
def loss(n: int) -> int:
    if n % 3 != 0:
        raise ValueError(...)
    return (n * 2) // 3  # Python 整数除法
```

**问题**：
1. **未体现 LCM 模环**：运算在普通整数环 ℤ 上进行，非 ℤ/LCM
2. **降维为欧氏算术**：整除检查 `n % 3 != 0` 是欧氏思维
3. **丢失拓扑意义**：损益操作是 T⁶ 环面上的平行移动，非普通算术

**正确实现**：

```python
# 正确实现 (LCM 模环):
def loss_in_lcm(n: int) -> int:
    """
    损一操作在 LCM 模环上:
    n ↦ (n * 2) / 3 mod LCM
    
    注意: 在 ℤ/LCM 环中，除以 3 等价于乘以 3 的模逆元
    """
    # 3 在模 LCM 下的逆元 (3^11 * 2^16 中 3 有因子，需特殊处理)
    # 实际上损益操作应在长度格点序列上进行，非任意整数
    return lcm_mul(n, MOD_INV_3)  # 需要预计算模逆元
```

#### 问题 2: 十二律链生成降维

```python
# 当前实现: 使用 round() 取整 (浮点近似!)
current = round((current * 2) / 3)  # 违宪! 使用了浮点近似
```

**严重问题**：使用了浮点 `round()` 进行取整，违反了律算宪法!

**正确实现**：十二律链应严格在整数格点上定义：

```python
# 正确实现 (严格整数格点):
TWELVE_LU_LENGTHS = [81, 54, 72, 48, 64, 43, 57, 38, 51, 34, 45, 30]

def get_twelve_lu_length(step: int) -> int:
    """获取十二律长度格点 (严格查表，非计算)"""
    return TWELVE_LU_LENGTHS[step % 12]
```

---

### 2.3 tq10_format.py (耦合域) - ⚠️ 部分降维

#### 问题 1: qs 存储为字节列表 (丢失 Tryte 拓扑)

```python
# 当前实现:
self.qs = qs or [0] * 6  # 6 个独立字节，无拓扑关联
```

**问题**：qs[6] 应逻辑上对应 **5 个 Tryte** (每 Tryte 6 trit) 的工程编码打包，而非 6 个独立字节。

**正确实现**：

```python
# 正确实现:
from .tryte import Tryte, PackedTryte5

class SovereignBlock:
    def __init__(self, trytes: List[Tryte] = None, ...):
        # 内部逻辑表示: 5 个 Tryte (30 trit)
        self.trytes = trytes or [Tryte([Trit.T1]*6)] * 5  # 默认平衡态
        
        # 物理打包表示: 6 字节 PackedTryte5
        self.qs = self._pack_trytes_to_qs(self.trytes)
    
    def _pack_trytes_to_qs(self, trytes: List[Tryte]) -> List[int]:
        """Tryte → qs[6] 打包 (地址翻译)"""
        # 30 trit → 6 字节 (5 trit/字节)
        ...
```

---

## 三、范畴偏离根源分析

### 3.1 降维模式识别

| 降维模式 | 代码位置 | 说明 |
|---------|---------|------|
| **浮点近似** | `loss_gain.py:round()` | 使用浮点 round() 取整 |
| **欧氏算术** | `loss_gain.py:n % 3` | 整除检查是欧氏思维 |
| **字节列表** | `tq10_format.py:qs` | 丢失 Tryte 纤维丛结构 |
| **模 3 算术** | `trit.py:gf3_add` | 降维为普通模运算 |

### 3.2 正确实现路线

```
律算正确实现路线:

根数学 (trit.py):
├── Trit 定义 ✅ 正确
├── 编码/解码 ✅ 正确
└── GF(3) 加法 ❌ 需改为驻波叠加表

耦合域 (loss_gain.py):
├── LCM 常量 ✅ 正确
├── 损益操作 ❌ 需改为 LCM 模环运算
└── 十二律链 ❌ 需改为严格查表

耦合域 (tq10_format.py):
├── 16 字节结构 ✅ 正确
├── 字段提取 ✅ 正确
└── qs 存储 ❌ 需改为 Tryte 列表 + 打包/解包
```

---

## 四、修正优先级

| 优先级 | 模块 | 问题 | 修正工作量 |
|--------|------|------|-----------|
| **P0 (紧急)** | `loss_gain.py` | 浮点近似 + 欧氏算术 | 小 |
| **P1 (高)** | `trit.py` | GF(3) 降维 | 小 |
| **P1 (高)** | `tq10_format.py` | qs 丢失拓扑 | 中 |
| **P2 (中)** | `tryte.py` | 无问题 | 无 |
| **P2 (中)** | `wuxing.py` | 无问题 | 无 |

---

## 五、修正计划

### 5.1 P0: 修正 loss_gain.py

```python
# 移除浮点 round()
# 使用严格查表或 LCM 模运算
# 移除整除检查 (改用模逆元)
```

### 5.2 P1: 修正 trit.py

```python
# 使用驻波叠加表替代模 3 算术
# 明确体现虚实对消灭
```

### 5.3 P1: 修正 tq10_format.py

```python
# qs 内部表示改为 Tryte 列表
# 添加 Tryte ↔ qs 打包/解包方法
# 保持拓扑完整性
```

---

## 六、宪法条款

> **工程实现必须严格遵循律算宪法的范畴定义：根数学使用 GF(3) 驻波叠加而非模 3 算术；耦合域使用 LCM 模运算而非欧氏整数除法；TQ1_0 格式中的 qs 字段必须保持 Tryte 纤维丛拓扑结构，禁止降维为独立字节列表。任何使用浮点近似、欧氏整除检查、字节列表的操作均属违宪。**
