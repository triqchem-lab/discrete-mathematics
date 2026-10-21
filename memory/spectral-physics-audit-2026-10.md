# 光谱物理审核报告（2026-10-22）：H₂O@C₆₀ · I_h · Δ=√3

> 约束：本报告所有物理/数学陈述的来源都是**本地文件**（源码 + `docs/wiki` + `scholar-loop` + `sov-math`）
> 或**联网检索到的论文原文**（逐条标 URL）。**未使用训练资料**。

## 一、本地形式化（逐个核实，均为 0 postulate / 0 hole）

| 模块（实际路径）| 行数 | 关键定理 |
|---|---:|---|
| `Synthesis/Physics/IhC60Vibration.agda` | 933 | `freq-46` / `dim-174` / `active-plus-dark` / `ir-active` / `raman-active` |
| `Application/Physics/H2OC60.agda` | 240 | `tr-equals-t6-dim` / `c60-modes-equals-toroidal` / `ground-state-match` |
| `Synthesis/Format/ParityViolation.agda` | 248 | `neutrinoLeftHandedOnly` / `parityViolationTheorem` / `weakForceIsomorphism` |
| `Foundation/EnergyGap.agda` | — | `energyGapSquared : Δ² ≡ 3`（载体 `Sqrt3` 代数数）|

## 二、数学内核：独立复算 + 文献吻合（**强** ✅）

| 恒等式 | 我复算的结果 |
|---|---|
| `Σ classSize` | **120** = |I_h| ✅ |
| `Σ m_R`（独立基频数）| **46** ✅ |
| `Σ m_R·d_R` | **174** = 3·60−6 ✅ |
| `144 = 120 + 24` = `12²` | ✅ |
| `6624 = 144 × 46` | ✅ |

**文献对照**（[diva-portal 学位论文](https://www.diva-portal.org/smash/get/diva2:140619/FULLTEXT01.pdf)）：
> 「**10 Raman active (2A_g + 8H_g)** and **four F₁ᵤ** odd parity infrared active modes」

⇒ 与我们的 `ir-active=4` / `raman-active=10` / `observed-lines=14` **精确一致** ✅

## 三、实验数据核对（**联网，论文原文**）

**PNAS 2012**，Beduz / … / Levitt / Murata，109(32):12894 · [全文](https://pmc.ncbi.nlm.nih.gov/articles/PMC3420201/)
**PRL 120, 266001 (2018)** · [arXiv:1802.00676](https://arxiv.org/abs/1802.00676)

| 我们的模型 | 实验 | 判定 |
|---|---|---|
| 转化时间 `~10 h` | **固相 3.5K = 12 ± 1.3 h** | ✅ 吻合 |
| （对照：室温溶液）| 30±4 s (¹⁶O) / 16±3 s (¹⁷O) | ✓ 两相不同，不可混比 |
| ortho 基态分裂 `0.52 meV` | INS **0.6 meV** / NMR **~0.9 meV** | ⚠ 差 13% |
| `6D TR ≅ T⁶ = GF(3)⁶` | 非对称陀螺 `J_KaKc`，确为 6 维 | ✅ 维数一致 · ⚠ 论文写「no obvious signature of **strong** TR coupling」|
| `Δ = √3` | 分裂 = 0.6 meV | ✗ **无已建关系** |

**Table 1（实验靶子）**：`000→101(下)` INS **2.3±0.1**；`000→101(上)` INS **2.9±0.1**；
`101→110` IR **2.5±0.6**；`000→011` IR **4.6±0.6**；`101→212` IR **7.0±0.6**（meV）。

## 四、★★ 审核出的**两处问题**

### (1) 算错的等式（**算术错误**）

`H2OC60.agda` 注释：**「0.52 meV = Δ/2 热阈值投影」** ✗
- `Δ/2 = √3/2 = **0.866 meV**` ⇒ 与 0.52 差 **66.5%** ✗
- 实测 0.6 与 `Δ/2` 也差 **30.7%** ✗
- **⇒ 该等式不成立** ✗ —— 而 `0.52` 与实测 `0.6` 只差 13%，**数据本身没错，错的是等式**

### (2) 「3:1 比值是几何签名」这句话**不成立**

`scholar-loop/examples/quartz_phonon_sqrt3_verify.py` 写：
> 「The 3:1 ratio is **NOT post-hoc** — it's the **geometric signature of Δ² = 3**」

**审核结论**：3:1 与 2:1 是**刚性转子**（`E_J ∝ J(J+1)`）的**必然结果** ✗ ——
固相与气相**都有**（固相 `4.60/2.30 = 2.000`、`7.00/2.30 = 3.043`），
**不需要** `Δ²=3` / 正四面体 / T⁶ 任何一个前提。
⇒ **它不是判别性证据** ✗。

## 五、★ 唯一有判别力的候选（**猜想，未推导**）

> **`groundStateSplitting × Δ ≈ 1`** ⇔ `splitting ≈ 1/Δ = 0.5773 meV`

- 实测 `0.6 × √3 = **1.039**` ⇒ 偏离 1 仅 **3.9%**
- **只对分裂成立** ✗：其他 5 条跃迁乘 Δ 分别为 `3.98 / 5.02 / 4.33 / 7.97 / 12.12`

**⇒ 若成立** ⇒ 分裂是**特殊的量**（而非普适换算因子）⇒ 这是一个**可检验的预言** ✅
**⇒ 若不成立** ⇒ 就是拟合，应丢弃 ✗

### **决定性的检验（待做，只差一个数字）**

查 `HF@C₆₀` 或 `H₂@C₆₀` 的基态分裂，看是否也满足 `splitting·Δ ≈ 1`。

**已有文献线索（但均被付费墙 / PDF 不可提取拦住）**：
- RSC Faraday Discuss 2018, 212:547 —「Effects of symmetry breaking on the TR eigenstates of **H2, HF, and H2O** inside C60」[PubMed 30226507](https://pubmed.ncbi.nlm.nih.gov/30226507/)
- RSC PCCP 2017 —「Explaining the symmetry breaking observed in the endofullerenes **H2@C60, HF@C60, and H2O@C60**」
- JCP 147, 244303 (2017) —「Potential energy and dipole moment surfaces for **HF@C60**」
- Southampton eprints —「The THz spectrum of **HF@C60** (5 K)」

## 六、诚实边界

1. **强的部分**：`freq-46` / `dim-174` / 选择定则（0-postulate + 独立复算 + 文献吻合，三重）✅
2. **弱的部分**：「46 三尺度同构」目前只是**同一个数字**，**没有** Agda 定理连接群论与宇称 ✗
3. **未建立**：`Δ=√3` ↔ 实验的**单位桥** ✗ —— 唯一候选是 `1/Δ`（3.9%），**未在第二体系验证** ✗
4. **未形式化**：`α=0.0583` / `0.45 eV` / `~10 h` 的定量推导

## 七、我**没有做**的事

未改任何物理常数、未改 `Aether.agda`、未改 wiki、未改 `scholar-loop` 数据、未改 `sov-math`。
（此前曾误改 `Aether` 注释，已 `git revert`，逐字复原。）
