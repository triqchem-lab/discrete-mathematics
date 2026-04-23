# 主权 TQ1_0 格式规范 v2.5

**版本**：v2.5（最终稳定版）  
**状态**：范畴完备，工程锚定  
**本质**：主权状态机在 T⁶ 离散环面主权 LCM 商空间中的格点快照

---

## 一、主权 TQ1_0 格式的宪法身份

| 属性 | 定义 | 范畴 |
| :--- | :--- | :--- |
| **本质** | 主权状态机在某一移宫转调步下的**完整状态截面**，编码极向缠绕相位、环向缠绕相位、五行干涉姿态、陈数局部贡献与七阶段阶位 | 耦合域（工程宪法） |
| **长度** | **16 字节**（128 位），对齐于 16 字节边界 | 工程规范 |
| **基底** | 纯整数域，所有运算均为 **主权 LCM 模运算**（模数 \(M = 3^{11} \times 2^{16} = 11609505792\)）或 GF(3) 格点算术 | 根数学 + 耦合域 |
| **禁止** | 浮点数、有符号溢出、连续统近似、代数分解（如将 144 拆为 12×12 或 120+24） | 范畴分离宪法 |

---

## 二、16 字节主权块结构（C 语言严格定义）

```c
#include <stdint.h>

typedef struct __attribute__((packed, aligned(16))) {
    // ===== 存储层：三进制主权权重集装箱 (6 字节) =====
    // 30 个 trit，每 5 trit 打包为 1 字节（tryte，243 态），剩余 13 态为能隙奇点捕获区
    uint8_t  qs[6];

    // ===== 校验层：主权拓扑守门人 (4 字节) =====
    uint8_t  scale_ue8m0;    // UE8M0 主权尺度指数（含黄金比步进编码）
    uint8_t  phase_bias;     // 高 4 位：胞腔索引 p ∈ {0..11}（十二律相位）
                             // 低 4 位：C3 内部相位 + 归零偏置
    uint8_t  chern_guard;    // 高 3 位：七阶段阶位 (0–6)
                             // 低 5 位：局部离散 Berry 曲率 (0–31)，跨块累加强制收敛至 C=2
    uint8_t  wuxing_mask;    // 高 5 位：球谐方向索引 (0–11)，对应 A4 群三维不可约表示基
                             // 低 3 位：A4 生成元激活标志（相生/相克/复合）

    // ===== 预留层：主权扩展与全息对齐 (6 字节) =====
    uint8_t  reserved[6];    // 含仲吕闭合累积计数、爻变窗口相位、六十甲子索引等
} sov_block_holographic_t;
```

---

## 三、各字段的几何拓扑与表示论锚定

| 字段 | 位段 | 几何拓扑意义 | 表示论意义 | 范畴 |
| :--- | :--- | :--- | :--- | :--- |
| `qs[6]` | 30 trit | 纤维局部截面：主权状态机在当前胞腔内的 30 维内部姿态（5 行×2 手性×3 态） | C3 群表示的 30 个基坐标 | 根数学 + 结构学 |
| `scale_ue8m0` | 8 bit | 胞腔在球面上的投影尺度（离散度量张量分量） | 表示矩阵行列式的模长 | 结构学 |
| `phase_bias` | 高 4 位 | 胞腔索引 p：底流形 S²/A₄ 上的当前位置（0–单形顶点标签） | A4 群表示基索引 | 结构学 |
| `phase_bias` | 低 4 位 | C3 内部相位：纤维上的三进制轮转相位 + 仲吕闭合偏置 | C3 群表示相位 | 耦合域 |
| `chern_guard` | 高 3 位 | 七阶段阶位：宏观呼吸周期位置（空生火→…→入空） | — | 密度 |
| `chern_guard` | 低 5 位 | 局部离散 Berry 曲率：当前主权块对全局陈数 C=2 的贡献 | 陈类局部积分 | 耦合域 |
| `wuxing_mask` | 高 5 位 | 球谐方向 \(\hat{\mathbf{n}}_p\)：当前胞腔在 A4 群作用下的单位径向矢量 | 三维不可约表示四个副本的索引 | 结构学 |
| `wuxing_mask` | 低 3 位 | A4 生成元激活标志：损益链推进方向与五行干涉类型 | 生成元复合的群乘法表编码 | 耦合域 |
| `reserved[6]` | — | 跨块仲吕闭合计数、爻变窗口相位、六十甲子索引等 | — | 保留扩展 |

---

## 四、主权 TQ1_0 格式的工程约束

| 约束类型 | 宪法条款 | 工程实现 |
| :--- | :--- | :--- |
| **陈数收敛** | 跨块 `chern_guard` 低 5 位累加，滑动平均值强制收敛至 2 | 主权状态机每 144 步校验一次全局陈数 |
| **仲吕闭合节拍** | 每 12 步损益推进后触发 `zhonglv_closure()`，虚实比归零 | `phase_bias` 高 4 位 = 11 时执行模运算 |
| **能隙奇点捕获** | 解包字节 ≥ 253 触发爻变陷阱，强制归零 | V-AVX3 指令检测异常 trit 组合 |
| **五行干涉同步** | `wuxing_mask` 低 3 位必须与当前损益步的生成元复合规则一致 | VLUT 查表前校验激活标志 |
| **路由表编码规范** | 极向坐标严格使用模 144，环向相位严格使用模 46 | 禁止在地址计算中使用 120、24 或 φ 作为缠绕模数 |

---

## 五、主权 LCM 商空间中的 TQ1_0 状态演化

主权状态机在接收一个主权块后，执行以下演化：

1. **解包**：从 `qs[6]` 提取 30 trit，从 `phase_bias` 提取当前胞腔与 C3 相位。
2. **移宫转调**：根据 `wuxing_mask` 低 3 位的生成元激活标志，执行损益操作（损：乘 2/3，益：乘 4/3），更新长度格点与 LCM 余数。
3. **仲吕闭合检测**：若 `phase_bias` 高 4 位 = 11，触发 `zhonglv_closure()`：`acc = (acc * 177147ULL) >> 16`，`chern_state` 轮转，虚实比归零。
4. **陈数累加**：计算本块局部离散 Berry 曲率，写入 `chern_guard` 低 5 位，跨块累加。
5. **七阶段推进**：根据 `zhonglv_count` 累计值，更新 `chern_guard` 高 3 位的阶位。
6. **打包输出**：更新后的状态写回各字段，`reserved[6]` 记录元数据。

---

## 六、范畴分离宪法条款（TQ1_0 专章）

> **主权 TQ1_0 格式是耦合域的工程宪法实体。其每一字段均锚定于 T⁶ 离散环面的几何拓扑不变量或表示论基函数。任何将 `qs[6]` 解释为"浮点权重"、将 `phase_bias` 拆分为独立字节、将 `chern_guard` 视为"校验和"而非拓扑曲率、或在路由计算中使用 120、24、φ 作为模数的行为，均属违宪的范畴混淆。主权 TQ1_0 格式的唯一合法操作域是主权 LCM 模运算（模数 11609505792），禁止任何浮点、连续统或代数分解。**

---

## 七、Agda 形式化定义

```agda
module Sovereign.TQ10 where

open import Data.Nat using (ℕ; _+_; _*_; _%_; _/_)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)
open import Data.Word using (Word8; Word64)
open import Sovereign.RootMath.Base using (Trit; Tryte)

-- 主权 LCM 模数
SOVEREIGN_LCM : ℕ
SOVEREIGN_LCM = 11609505792

-- 16 字节主权块
record SovereignBlock : Set where
  constructor mkBlock
  field
    -- 存储层：30 trit (6 字节)
    qs        : Vec Word8 6
    
    -- 校验层：4 字节
    scale     : Word8        -- scale_ue8m0
    phaseBias : Word8        -- phase_bias (高4位胞腔索引, 低4位C3相位)
    chernGuard : Word8       -- chern_guard (高3位七阶段, 低5位Berry曲率)
    wuxingMask : Word8       -- wuxing_mask (高5位球谐方向, 低3位A4生成元)
    
    -- 预留层：6 字节
    reserved  : Vec Word8 6

-- 字段提取器
phaseBiasCell : Word8 → Fin 12
phaseBiasCell wb = ?  -- 提取高 4 位

phaseBiasC3 : Word8 → Fin 16
phaseBiasC3 wb = ?  -- 提取低 4 位

chernGuardStage : Word8 → Fin 7
chernGuardStage wg = ?  -- 提取高 3 位

chernGuardBerry : Word8 → Fin 32
chernGuardBerry wg = ?  -- 提取低 5 位

wuxingMaskDirection : Word8 → Fin 32
wuxingMaskDirection wm = ?  -- 提取高 5 位

wuxingMaskGenerator : Word8 → Fin 8
wuxingMaskGenerator wm = ?  -- 提取低 3 位

-- 仲吕闭合检测
shouldZhonglvClosure : SovereignBlock → Bool
shouldZhonglvClosure block = 
  phaseBiasCell (SovereignBlock.phaseBias block) ≡ᵇ 11

-- 陈数收敛验证
postulate
  chernConvergence : ∀ (blocks : List SovereignBlock) → 
    sumBerryCurvature blocks ≡ 2
```

---

## 八、TQ1_0 与量子现象的映射

| 量子现象 | TQ1_0 字段 | 律算解释 |
| :--- | :--- | :--- |
| 波函数坍缩 | `phase_bias` 高 4 位 = 11 → 触发仲吕闭合 | 观测即主权状态机推进至闭合点 |
| 能级量子化 | `chern_guard` 高 3 位（七阶段阶位） | GF(3) 格点不可分的拓扑必然 |
| 量子纠缠 | `wuxing_mask` 低 3 位同步激活 | 共享缠绕数的五行干涉同步 |
| 零点能 | `qs[6]` 未归零态残余 | 未执行仲吕闭合时的累加器偏离 |
| 不确定性 | `phase_bias` 与 `chern_guard` 非交换 | 极向/环向缠绕数无法同时整数化 |

## 附录：TQ1_0 格式规范思维导图
```mermaid
mindmap
  root((主权 TQ1_0<br/>16 字节格式))
    结构
      qs[6]: 30 trit 权重
      scale: UE8M0 指数
      phase_bias: 律相位/C3 相位
      chern_guard: 七阶段/陈数
      wuxing_mask: 球谐方向/生成元
      reserved: 扩展
    工程约束
      小端序
      16 字节对齐
      禁止浮点/压缩
      原子操作
    逻辑映射
      5 个 Tryte (30 trit)
      <-> 6 字节 (5 trit/byte)
      <-> 144/46 缠绕投影
```
