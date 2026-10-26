# 交接：多面体群 / 内嵌富勒烯线（更新于本会话末）

> 接手先读这一页，再跑 `bash engineering/run_line_checks.sh`（9 项全绿 = 环境正常）。
> 权威在台账（`proof_dag`）与源码；本页只做索引与边界。

## 一、这条线在做什么

量子受限光谱：H₂O/HF/H₂ 内嵌 C₆₀（I_h 笼）的转动-平动（TR）量子态与光谱分裂。
可形式化的部分落成 Agda 定理；只能计算的部分落成可复跑脚本（oracle），两者严格分开。

## 二、Agda 定理（内核通过，回执见台账）

| 模块 | 内容 | 回执 |
|---|---|---|
| `Synthesis/Physics/IhGroup.agda` | A5Card=60、IhCard=120、`ih-polar-decomposition : PolarWinding ≡ IhOrder + MerkabaOrder` | `c024f1ed…` |
| `Synthesis/Physics/IhDecomposition.agda` | 1+15+20+24=60、60+60=120、2×12=24、120+24=144 | `45bb1432…` |
| `Synthesis/Physics/PolyhedralReps.agda` | Σdᵢ²=\|G\|（A₄/A₅/2A₄/2A₅/I_h）、类大小和、轨道-稳定子 | `46b697b0…` |
| `Synthesis/Physics/IhC60Vibration.agda` | `freq-46`、`dim-174`、`vib-vector` | `28fef4c6…` |
| `Synthesis/Physics/NoSplitJ1.agda` | 对角情形不劈裂（`no-split-diag`） | `53f331b3…` |
| `Synthesis/Physics/NoSplitJ1Full.agda` | 一般情形不劈裂（`no-split-full`）+ 生成元阶 `shift³`/`flip²`/`g³` | `c9d1e186…` |
| `Synthesis/Physics/NoSplitJ1Ring.agda` | **任意无挠交换环**上的一般情形不劈裂（`no-split-ring-general`）+ 生成元阶；§9b 内核核验「推广蕴含 ℤ 版 `no-split-full`」 | `7890fd1c…` |
| `Synthesis/Physics/TRMultipletsZ.agda` | `sq-suc-Z`：ℤ 上 `x²+(2x+1)=(x+1)²`（TR 维数恒等式的代数核心） | `6f4517ba…` |
| `Synthesis/Physics/TRMultipletsNat.agda` | `sum-odd`：**完整 ℕ 索引版** `sumOdd a n + a² ≡ (a+n)²` + 4 实例 | `05743ad7…` |

**核心物理结论**：A₄ 不变的微扰只能是标量 ⇒ **劈不开 J=1 三重态**（Agda 定理，非数值；ℤ 版 `no-split-full` 与**任意无挠交换环**版 `no-split-ring-general` 都已证，后者覆盖 ℚ/ℝ/GF(p≠2) 系数）。

## 三、oracle（计算证据，非定理）

| 事实 | 脚本 | 回执 |
|---|---|---|
| {shift,flip} 闭包 = 12 阶 = A₄ | `engineering/verify_a4_closure.py` | `56921d3e…` |
| A₅ 25/25、I_h 100/100 特征标正交性（ℚ(√5) 精确，偏差 0） | `engineering/verify_polyhedral_characters.py` | `137d3638…` |
| 1770 顶点对 → 23 轨道，Burnside 23.0 | `engines/h2o_c60/verify_ih_orbits.py` | `bcc903b0…` |
| V6 在 J=1..6 的簇大小 ∈{1,3,4,5}（=I_h 不可约维数） | `engines/h2o_c60/verify_v6_structure.py` | `8bbb1ee6…` |
| ℓ=6 不变子空间 **rank=1**（系数唯一到标度） | `engines/h2o_c60/verify_v6_uniqueness.py` | `6bec8421…` |
| NSE Laplacian 秩 454 / 核 275（GF(3) 精确） | `engineering/verify_nse_rank6.py` | `c9942a18…` |
| 与 shift、flip 都交换的 3×3 矩阵必为标量（GF(3)^9 全穷举 19683 + GF(p)/ℚ 精确消元维数 1；GF(2) 反例 ⇒ 无挠性不可去） | `engineering/oracle_nosplit_ring_general.py` | `fea7e790…` |

## 四、一键回归

```bash
bash engineering/run_line_checks.sh    # 9 项，全绿才算环境正常
```

含：数据校验、拟合诊断、轨道、特征标、A₄ 闭包、V6 结构、V6 唯一性、NSE 秩、文档回执对账。
**负向控制已验证**：注入必失败项时会报 ❌ 并 exit 1。

## 五、数据一到就能算

```bash
python3 -m engines.h2o_c60.fit_v6 --j3 <J=3 笼致分裂 (cm^-1)>
```
输出每档 s 下的 V₆、推荐值与相对带宽。往返自检误差 0.00%。
**一条 J=3 数据即可定 V₆ 到 ±15%**（分裂 ~1 cm⁻¹）或 ±4%（~3 cm⁻¹）。

## 六、模型的可信度

| 环节 | 状态 |
|---|---|
| V₆ 的 I_h 不变性 | ✅ Agda + 数值结构 |
| V₆ 的系数 | ✅ 唯一到标度（rank 1） |
| 转动部分 | ✅ 自由转子 J=1 与教科书差 0.022 cm⁻¹ |
| 对称破缺项 V₂ 的剩余对称性 | ✅ 实测为 **D₂ ≅ V₄**（不是 C2v） |
| s（受阻标度） | ⚠ 未知；H₂ 类比 0.73，H₂O 需 ≈0.22 |
| **V₆ 数值** | ⏳ 只差一个 J=3 或 INS 数据点 |

## 七、明确的未完成项

1. **TR 维数恒等式**：✅ **已完成** —— `TRMultipletsNat.sum-odd : ∀ (a : ℤ) (n : ℕ) →
   sumOdd a n + a² ≡ (a+n)²`（回执 `05743ad7…`），含 4 个 l/J 实例（9/25/35/49，均 refl）。
   距最终形式 `Σ_λ(2λ+1)=(2l+1)(2J+1)` 只差 `a = J∸l`、`n = 2l+1` 的实例化（需 monus 与 l≤J）。
2. **闭包 = 12 元素**未在 Agda 形式化（由 oracle 承担）。
3. **本征值 → 能级**的线性代数环节未形式化。
4. 若真实位点对称性是 C2v/Cs，需把 V₂ 换成两分量四极项（未知量 +1）。

## 八、硬边界（写论文必带）

1. **144 ≠ \|I_h\|**：\|I_h\|=120；144 = 120 + 24，24 有 `2A₄` 与 `A₄×C₂` 两种实现。
2. **\|2A₅\|=120=\|I_h\| 但 ≇**（I_h 无 4 阶元）。
3. **A₄ 劈不开 J=1**（已证）；能劈开的是 C2v/C2/C3/C5 一档。
4. 预测网格的 `J3_cage_split` 用**能级追踪**（不是排序），|V₆|≳0.5 时强烈非线性；
   `J3_first_order` 只在一阶区（|V₆|≲0.1）可信。

## 九、等人类裁决的事

- `Aether.agda` / `Zhonglv.agda` 的**假 postulate**（内核已证否，模块不一致）——改公理需人类裁决。
- artifact 依赖门禁语义（artifact 永不 proven ⇒ 下游被锁死）。
