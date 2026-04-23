# 律算合一外部依赖审计报告

**日期**: 2026-04-23  
**审查原则**: 所有外部引用（Agda 标准库）初始信用为 **0**，必须经过高维几何审查才能信任。

---

## 1. 循环依赖检测

✅ **未发现循环依赖**。模块依赖图是 DAG (有向无环图)。

---

## 2. 关键外部依赖链 (信用0)

共发现 **26 个外部依赖模块**，初始信用均为 **0**。以下标记为 `UNTRUSTED` 的引理**禁止直接用于宪法级证明**。

### 🔴 极高风险 (CRITICAL) - 算术与模运算

| 外部模块 | 引用次数 | 污染模块 | 风险描述 |
|:---|:---|:---|:---|
| `Data.Nat.Properties` | 3 | `Coding/Trit.agda`, `Coupling/LCM.agda`, `Coupling/TrainingSoftConstraint.agda` | 模运算分配律 `+-mod`、乘法模零律 `m*n%m≡0` 基于连续统算术，**与 T⁶ 离散拓扑可能冲突** |
| `Data.Nat.DivMod` | 4 | `Base/Axioms.agda`, `Coupling/LCM.agda`, `Coupling/Zhonglv.agda`, `RootMath/DigitalRoot.agda` | 除法 - 模分解 `div-mod` 未经验证，**可能破坏 Base-3 编码的互逆性** |

### 🔴 高风险 (HIGH) - 同伦类型论基础

| 外部模块 | 引用次数 | 污染模块 | 风险描述 |
|:---|:---|:---|:---|
| `Cubical.Foundations.Prelude` | 19 | 所有 HoTT 模块 + RootMath/Base.agda | `Path` 类型假设连续空间，**与离散 T⁶ 环面拓扑不兼容** |
| `Cubical.Foundations.Equiv` | 1 | `HoTT/Equivalence.agda` | 等价性定义基于连续同伦，需离散化 |
| `Cubical.Foundations.HComp` | 1 | `HoTT/Fibration.agda` | 高等组合子未经验证 |

### 🟡 中风险 (MEDIUM) - 基础类型

| 外部模块 | 引用次数 | 风险描述 |
|:---|:---|:---|
| `Data.Nat` | 46 | 自然数定义可能兼容，但需确认与缠绕数 (144, 46) 的对齐 |
| `Data.Fin` | 33 | 边界检查需与极向/环向缠绕数严格对齐 |
| `Data.Vec` | 24 | `map` 需证明保持纤维丛结构 |
| `Data.Complex` | 2 | `Structology/DiscreteCalculus.agda` 使用复数，**违反纯三进制宪法** |

---

## 3. 基本链路审查

### 链路 1: 根数学 → LCM → 状态机
```
RootMath/Base.agda 
  → Data.Nat [UNTRUSTED]
  → Data.Nat.Divisibility [UNTRUSTED]

Coupling/LCM.agda 
  → Data.Nat.Properties [UNTRUSTED] ⚠️ 极高风险
  → Data.Nat.DivMod [UNTRUSTED] ⚠️ 极高风险

Engine/StateMachine.agda 
  → Data.Nat [UNTRUSTED]
```

**审查结论**: 此链路中 `LCM.agda` 直接使用了未审查的模运算引理 (`+-mod`, `m*n%m≡0`)。如果这些引理与 T⁶ 离散拓扑冲突，**整个打包/解包互逆性证明将失效**。

### 链路 2: 纤维丛 → 联络 → 等价性
```
HoTT/Bundle.agda 
  → Cubical.Foundations.Prelude [UNTRUSTED] ⚠️ 高风险

HoTT/Connection.agda 
  → Cubical.Foundations.Prelude [UNTRUSTED] ⚠️ 高风险

HoTT/Equivalence.agda 
  → Cubical.Foundations.Equiv [UNTRUSTED] ⚠️ 高风险
```

**审查结论**: HoTT 层完全依赖 Cubical Agda 的连续同伦理论。`Path` 类型、`Glue` 类型等可能与离散 T⁶ 环面冲突。**所有 HoTT 证明需要离散化重写**。

---

## 4. 信任污染矩阵

以下 **7 个模块** 被标记为**已污染**，其证明结果不可信：

| 模块 | 污染源 | 影响范围 |
|:---|:---|:---|
| `Coding/Trit.agda` | `Data.Nat.Properties` | GF(3) 运算基础不可信 |
| `Coupling/LCM.agda` | `Data.Nat.Properties`, `Data.Nat.DivMod` | **打包/解包互逆性证明无效** |
| `Coupling/TrainingSoftConstraint.agda` | `Data.Nat.Properties` | 软约束阈值计算不可信 |
| `Base/Axioms.agda` | `Data.Nat.DivMod` | 公理体系基础不可信 |
| `RootMath/DigitalRoot.agda` | `Data.Nat.DivMod` | 数字根公理不可信 |
| `Coupling/Zhonglv.agda` | `Data.Nat.DivMod` | 仲吕闭合逻辑不可信 |
| `HoTT/ChernConservation.agda` | `Relation.Binary.PropositionalEquality.Properties` | 陈数守恒证明不可信 |

---

## 5. 修复计划

### 阶段 1: 创建信任边界 (Trust Boundary)
- [x] 创建 `Sovereign.Trust.External` 模块，标记所有外部引用为 `UNTRUSTED`。
- [ ] 在宪法文档中声明信任边界。

### 阶段 2: 高维几何重新证明
- [ ] 在 `Sovereign.RootMath.Arithmetic` 中重新证明模运算引理：
  - `+-mod`: 模运算分配律 (基于 GF(3) 格点)
  - `m*n%m≡0`: 乘法模零律 (基于离散环面)
  - `mod-<`: 模小于除数 (基于缠绕数)
- [ ] 在 `Sovereign.HoTT.DiscreteCubical` 中重新定义离散 Path 类型。
- [ ] 移除 `Data.Complex` 引用，使用代数数替代。

### 阶段 3: 依赖替换
- [ ] 将 `Coupling/LCM.agda` 中的 `Data.Nat.Properties` 替换为高维几何版本。
- [ ] 将 HoTT 层中的 `Cubical.Foundations.Prelude` 替换为离散版本。

---

## 6. 审查协议 (Review Protocol)

任何外部引理必须经过以下步骤才能标记为 `TRUSTED`:

1. **高维几何对齐**: 证明引理与 T⁶ 离散环面拓扑兼容。
2. **离散化验证**: 在 GF(3) 格点上重新证明。
3. **宪法审查**: 由律算宪法审查员签字确认。
4. **形式化证明**: 在 Agda 中完成结构化证明 (非 postulate)。

---

**审查结论**: 当前代码库存在 **严重的信任链污染风险**。核心宪法模块 (`LCM.agda`, `HoTT/*.agda`) 直接引用了未经验证的外部算术引理，可能导致高维几何证明的逻辑崩溃。

**建议立即执行阶段 1 和阶段 2 的修复。**
