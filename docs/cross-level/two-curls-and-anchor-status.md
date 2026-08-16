# 两种旋度定位与 8 锚点状态（正式记录）

> 固化「共轭与旋度交换」的精确区分，防止未来混淆。日期：2026-08-16。

---

## 一、两种旋度的最终定位

| 旋度类型 | 定义 | σ 交换性 | 承载意义 |
|:---|:---|:---|:---|
| `curl9std`（标准分量旋度） | 逐分量标准 GF(9) 旋度 | ✅ `curl-sigma-comm` | **代数对称**：σ 与空间微分运算交换，保证共轭相位在空间传播中守恒 |
| `curl9`（共轭旋度） | 实部=∇×B，虚部=−∇×E | ❌ 不交换，被投影定理替代 | **物理分离**：E/B 的动力学分离直接编码在定义中 |

**两个层面的真理**：
- **代数层面**的 σ 同态性 → `curl-sigma-comm`
- **物理层面**的 E/B 投影分离 → `reVec-curl9` / `imVec-curl9`

两者不能互相替代，都是必需。实现于 `src/Sovereign/Physics/DiscreteMaxwellGF9.agda`
§5（共轭旋度 + 投影定理）与 §7（标准旋度 + `curl-sigma-comm`）。

---

## 二、8 锚点状态（全部 0-postulate，编译通过）

| # | 锚点 | 定理 | 位置 |
|---|---|---|---|
| 1 | 标量无旋 | `curl-grad-zero` | DiscreteEMField3D |
| 2 | 旋度输运无损耗 | `flux-diff` | EntropySpinMicro |
| 3 | 质量量子化 | `quantized-mass` | EntropySpinQuantize |
| 4 | 熵旋源仅沿 n̂ | `divS-identity` | EntropySpinVerification |
| 5 | 无源旋度通量为零 | `curl-flux-vanishes` | VectorFieldGeometricPhase |
| 6 | 矢量场量子化 | `vector-quantization` | VectorFieldGeometricPhase |
| 7 | 共轭与时间交换 | `σ-time-comm` | DiscreteMaxwellGF9 |
| 8 | σ 与标准旋度交换 | `curl-sigma-comm` | DiscreteMaxwellGF9 |

---

## 三、两个新原生锚点（本轮固化为微模块）

| 锚点 | 定理 | 模块 |
|:---|:---|:---|
| 根号二原生存在（α²=2） | `alpha-squared-is-root-two`（refl） | `RootTwoGF9.agda` |
| 三步回归原点（C3 周期 3） | `three-steps-return-origin`（refl） | `RootTwoGF9.agda` |
| 可见光可观测（结构角=采样角=90°） | `visible-light-observable`（refl） | `ObservabilityAngle.agda` |

**诚实边界**：
- 自转频率 2.92×10⁸、r/R=√2 的几何量化、质量=频率派生 → 仍不可形式化（候选）。
- 感官角度采样序列的 5.625°（原文 5.5125° 为疑似笔误）已按 1/64 转 = 5.625° 修正。
