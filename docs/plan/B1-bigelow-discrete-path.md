# B1 研究报告：Bigelow 定理的离散证明路径

> 课题 B1（P1）｜六节结构｜2026-10-11
> 人类口径：不硬开理由=**工作量过大+依赖连续拓扑工具**（非违红线）；本报告钉实或否定「显式核元素验证」路线
> **结论先行：路线钉实——Bigelow 原文含显式核元素（词长 120），定理可在本地以「见证+双离散验证」形式化（~250-450 行+oracle）**

---

## 一、数学对象

**定理（Bigelow 1999）**：
```
burau-not-faithful : ∃ w ∈ B₅, w ≢ e × burau₅(w) ≡ I
```
- Burau 表示：B_n → GL_{n-1}(ℤ[t,t⁻¹])（约化形 4×4 对 B₅）；
- **陈述是离散命题**（辫词/Laurent 矩阵——零连续对象）；Bigelow 的**证明**用穿孔圆盘上的曲线+代数相交数（几何拓扑工具）。

## 二、经典路径（文献钉实——三问全答）

**① Long-Paton 1993**：证 **n≥6** 不忠实（非 n=5——把 Moody 的 n≥9 降到 n≥6）；方法=**显式给出核中新元素的辫词表示**（概要卡 §1.2）；Topology 32 (1993)。
**② Bigelow 1999**（[arXiv:math/9904100](https://arxiv.org/abs/math/9904100)，[GT 3 (1999) 397-404](http://www.emis.mi.sanu.ac.rs/emis/journals/UW/gt/GTVol3/paper16.abs.html)）：
- 方法：穿孔圆盘上简单闭曲线 α/β + **代数相交数** `(t^k α̃, β̃)`（提升圆盘上的相交对）——Casson 型不变量思想；
- **显式性（关键实测——pdftotext 全文提取）**：论文**明文给出显式核元素**：
  ```
  ψ₁ = σ₃⁻¹σ₂σ₁²σ₂σ₄³σ₃σ₂                （送 α 至直线弧 q₄→q₅）
  ψ₂ = σ₄⁻¹σ₃σ₂σ₁⁻²σ₂σ₁²σ₂²σ₁σ₄⁵          （送 β 至直线弧 p₀→q₅）
  核元素 w = [ψ₁⁻¹σ₄ψ₁, ψ₂⁻¹σ₄σ₃σ₂σ₁²σ₂σ₃σ₄ψ₂]   —— 词长 120
  ```
  原文自述「**The proof of Theorem 1.4 gives an explicit non-trivial element of the kernel**」；曲线由计算机搜索找到（Figure 3），「simple enough to check by hand」；
- 另给 B₆ 例：[ψ₁⁻¹σ₃ψ₁, ψ₂⁻¹σ₃ψ₂]；
- n=4 侧：计算机搜索表明满足条件的弧对必相交 ≥500 次（倾向忠实但非证明）——**n=4 仍开**。
**③ Moody 1991**：n≥9 不忠实（[Zbl 0751.57005](https://zbmath.org/?q=an%3A0751.57005)）；**④ 显式核元素**：**有**——Bigelow 原文即给出（上式）；且 Gibson-Williamson-Yacobi（[arXiv:2310.02403](https://ar5iv.labs.arxiv.org/html/2310.02403)，2023）明言「unable to rediscover **Bigelow's (integral) kernel elements for n=5 and n=6**」——确认 Bigelow 有整系数核元素可算。

**离散化已有实证（世界面）**：
- **Bigelow 自己的 C 实现**（freshbugs/burau4 iv.c——参数化曲线族搜索）；
- **fuglede/burau**（[Python 包](https://raw.githubusercontent.com/fuglede/burau/f425d38c0a8f542470627ced1cf72755fa76fa8e/README.rst)）：Bigelow 方法的完整实现——相交数=「停车场各层」的**有限枚举**（每个交点贡献 ±t^k），核元素 ⟺ 多项式为空字典——**「Casson 型不变量」在此构造下本来就是离散可计算量**（有限交点+层数计数）；
- G-W-Y 2023：** reservoir sampling 算法**找 B₄⊗F₅ 核元素（Garside 长 5411）——纯计算路线。

## 三、本地对接（锚点实测）

| 本地件 | 锚点 | 对接 |
|---|---|---|
| BurauCubical（Mat3=ℤ→ℤ 函数系数矩阵；braid-rel；rearrange9 :261；assoc-entry :380 面） | `Algebra/BurauCubical.agda:187` | **B₃ 载体**（3×3=未约化 Burau of B₄ 先例）——**B₅ 需 Mat4 推广**（~50-80 行同范式） |
| BurauRep（B₃→GL₂(ℤ[t,t⁻¹]) 定义层） | `Algebra/BurauRep.agda:15` | 定义层范式 |
| BurauInverse（s1-inv 件） | `Algebra/BurauInverse.agda:69` | σ⁻¹ 矩阵件范式（ψ₁ 的 σ⁻¹ 需求直用） |
| LaurentPolynomialFull（List (ℤ×ℤ) 载体） | `Algebra/LaurentPolynomialFull.agda:12-31` | 系数域候选 |
| LaurentFn（有限支撑函数 f:ℤ→ℤ） | `Algebra/LaurentFn.agda:20-36` | **函数表示**（canon-sums-unique=funExt 一行——推荐载体） |
| LaurentRingLaws/LaurentCanon/LaurentSums/LaurentMulAssoc/LaurentDistrib/LaurentSort | 全族（回执 5fefb4cc 等） | 环律/规范形/求和——矩阵乘法的内核 |
| NotFaithful 口径模板 | `TrivialRepUnfaithful:58-64`（Faithful/NotFaithful=Σ x, x≢e × ρx≡0）+ `_PK10:170-174`（NotFaithfulT） | **陈述模板直用**：`NotFaithful burau₅` |

## 四、严格设计（本地验证件的可执行方案）

**定理的离散验证结构**（不需要形式化 Bigelow 的几何证明——**见证+验证**路线）：
```
目标：burau₅-not-faithful : NotFaithful (burau₅)      -- Σ w, w ≢ e × burau₅ w ≡ I
```
- **见证 w**：Bigelow 的 120 词（字面编码：ψ₁/ψ₂ 生成元积+换位子结构）；
- **验证一（主件）**：`burau₅ w ≡ I`——120 次 4×4 Laurent 矩阵乘法。
  - **oracle 前置**（compute-then-verify）：Python 精确整数先算全部**中间矩阵**（分 ~10-12 段，每段终点矩阵的系数表落清单）；
  - Agda 侧：分段引理（每段 `refl` 对 oracle 中间值——附录 15 B1 abstract 封装预案 + #53 爆点对照——120 词的规范形逐段固化，**不许一次大 refl**）；
- **验证二（非平凡性）**：`w ≢ e`——**t 特化同态**：Burau₅ 在 t=-1（或 t=2）的特化是群同态 B₅→GL₄(ℤ)；算出特化矩阵 ≠ I ⟹ w ≢ e（**纯整数矩阵计算**——离散，~30-50 行）。⚠ 换位子的指数和=0（阿贝尔化失效）——t 特化是正解。
- **诚实标注**：几何面（为何该 w 在核中/为何 w≢e 的 Bigelow 原证）=**外部定理引用**（E 类）——本地只验**见证的两个代数性质**（矩阵恒等+t 特化非恒等）——两者皆为有限计算。

**规模重估（诚实）**：原估 100-200 行按「短词验证」估——实际 w 长 120 ⇒ 分段验证+Mat4 件+特化件 ≈ **250-450 行 + oracle 回执**（预算调整如实）。

## 五、诚实边界
| 面 | 状态 |
|---|---|
| **可形式化（推荐开工）** | ①Mat4/Burau₅ 定义层（~80）②w 的字面编码+分段验证（oracle 中间值——~150-250）③t=-1 特化非平凡性（~30-50）④NotFaithful 收口（~20） |
| **外部定理引用（E 类标签）** | Bigelow 的几何论证（曲线存在性/相交数计算的正确性/Theorem 1.4 本身）——本地不重证；fuglede/burau 的搜索算法=工具面 |
| **不硬开面** | n=4 忠实性问题（开问题）；一般 n 分类 |
| **研究级备选** | 若分段验证在 Agda 爆堆（#53/#15 族风险）：(a) t 特化矩阵验证先行（b）改证 mod-5 特化（B₄ 模 5 G-W-Y 已有先例——需 F₅ 面）(c) Bigelow 的相交多项式离散化（fuglede 算法形式化——研究级） |

## 六、依赖与优先
- **前置**：Laurent 线全 ✅（回执族）+ Mat3 范式 ✅；**新增 Mat4**（推广件——唯一新机件）；
- **下一步**（建议）：①**Python oracle**：按 Bigelow 词算分段中间矩阵+ t=-1 特化（`engineering/` 轨道——半天）②oracle 数据齐 ⇒ Agda 验证件开工（~250-450 行，探针先行）；
- **优先级**：P1——**离散路径钉实成立，建议由「不开」升为「待开工」（等人类点名）**。

## E 类标签
Bigelow n≥5=外部定理（引用陈述）；本地形式化=**见证验证**（上述设计）——不形式化其几何证明。
