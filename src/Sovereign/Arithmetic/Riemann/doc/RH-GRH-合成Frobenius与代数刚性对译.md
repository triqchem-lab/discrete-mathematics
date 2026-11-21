# 有限域补全工程 vs 原生 Frobenius 路线

> **定位**：对 Alpöge/Claude 2026-11 Lean 证明（镜像 `CocoSgt/riemann-hypothesis-lean`）的结构性对译，
> 以及 Sovereign GF(3^k) 路线的下一步路线图。
>
> **权威层级**：Agda 证明库 > 大衍四极框架 > 本文档 > LLM 分析。
> 本文档只做**结构诊断与路线规划**，不宣称连续 RH 的真伪；连续 RH 的形式状态以独立构建 + `#print axioms` 结果为准。
>
> **前提阅读**：`RH-GRH-三重完备性与离散闭合.md`（三重完备性条件二）、
> `docs/cross-level/frobenius-vs-conjugation-erratum.md`（原生 vs 外挂精确化）、
> `docs/Riemann/RH-GRH-文献检索与元理论断层诊断.md`（五大路线诊断）。

---

## 零、结论先行

1. **他不是在特征 0 里发现了 Frobenius，而是合成了 Frobenius 的全部功能。**
   四层代理：2-进分圆塔的 Frobenius **共轭类**、Behrend 厚集、θ-lift 链、ℓ-adic 除性钉扎 + √q 手工归一化。

2. **代码里有直接的反向证据**：`BaseCaseFalse` 在 ℚ 上被**证明**——最朴素的 p^N Frobenius 幂替换种子在 ℚ 上失败。
   这是「对整数求导不可能」的形式化版本，精确印证我们「条件二：特征 0 无原生 Frobenius」的诊断。

3. **代码里没有 GF(q) → ℚ 的函子**。GF(2^s) 从未作为一个域对象出现。所谓「有限域 → 无限域」不是提升（lift），
   而是**逐项功能替换**（functional substitution）。

4. **「他们没证明什么」这句话不能按字面说**。形式定理 `RiemannHypothesis` 用的是 Mathlib 官方定义，
   若构建通过且公理干净，在 Lean 社群标准下连续 RH 即已被形式证明。
   准确说法是：**证明的构造内容是补课程，不是发现新结构**——17.4 MB 源码的主体工程量在合成代数刚性。
   我们的批评是结构/方法论层面的，不是指控造假。对外措辞必须守住这条线。

5. **我们的下一步不是追赶连续 RH**，而是：(a) 把条件二升级为三层判据，(b) 把 θ-lift 链退化成 GF(3^k) 上的
   Frobenius 迭代，(c) 建立离散判据 ⇔ 连续零点线的对译字典——这是目前最大的真实缺口。

---

## 一、有限域 → 无限域：六段转换链（全部）

### 段 0：种子在 ℚ 上被证伪

- `Formalism/FrobeniusBaseCase/Statement.lean:174`：

  ```lean
  def BaseCaseFalse : Prop := ∀ l i : ℕ, l.Prime → 3 ≤ l → Odd i → 3 ≤ i →
    ∃ D : Data ℚ Unit (Fin 2), D.l = l ∧ D.i = i ∧ ¬ D.InW D.zvec
  ```

- 该命题有真实证明：`Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseFalseGeneralHolds.lean`。
- 有限域侧的机制本身是成立的：`.../Proofs/HasUniqueFixedPoint.lean:86` 的 `frobeniusSubstSpec` 是真证明，
  `Data.q := D.l^2` 扮演 GF(l²)，`ChainI` 中 `X d^(q^s)` 与 `eNum l s = ((l^2)^s−1)/(l^2−1)` 是 |C(F_{q^s})| 型几何和。
- **意义**：Stepanov 最朴素的「p^N 次 Frobenius 替换」在 ℚ 上直接失败。他必须换路，而换路的全部代价就是后面五段。

### 段 1：在 2^k 里补出 Frobenius 共轭类

- `Formalism/BehrendSets/Statement.lean:9-19`：

  ```lean
  abbrev OrdGrp (s) := (ZMod (2^(s+2)))ˣ ⧸ ±1
  def frob (s l) := l 在 OrdGrp s 中的类
  def OrdIff : orderOf (frob s l) ≤ 2^j ↔ l ≡ ±1 [ZMOD 2^(s+2-j)]
  ```

- 这是 2-进分圆塔 Gal(ℚ(ζ_{2^{s+2}})/ℚ) 中素数 l 的 Frobenius **共轭类**。
  `OrdIff` 把「阶小」翻译成「l ≡ ±1 mod 2^k」——功能上对应 GF(2^s) 的 Frobenius 轨道短 / 分裂早。

- **关键限定**：这是商群里的一个**共轭类/阶**，不是域上的双射自同构。
  它保留了「轨道长度」这一个维度，丢掉了 `x ↦ x^p` 的**算术强制**与**逆映射**。
  这正是我们勘误文档说的：char 0 里唯一缺的不是「自同构资格」，而是幂映射式的算术强制与典范唯一性。

- **代码事实**：`OrdIff` / `OrdCard` 在整个仓库只以 `def : Prop` 出现，未见证明定理，也未在主定理链中被断言或使用。
  也就是说，这一层在当前代码里更接近**规格说明**（需要什么），而不是主链的已证输入。

### 段 2：Behrend 厚集补 Stepanov 行列式的非零性

- `BehrendFree` / `BehrendBound` / `ThickSet` / `WindowTwo` / `OrbitOne` / `TranslateMean`（同文件 48-90 行）。
- `BehrendSets/BehrendVariance/Select.lean` 的 `select`，在 `BehrendSets/TranslateMean.lean:11` 导出为
  `theorem select : Select`——**这一层是真实证明的**，不是规格。
- 有限域上行列式非零靠交点数（正性定理）；特征 0 上靠 B 进制展开唯一性
  （`coeff_zero`: ∑ c_m B^m = 0 → c_m = 0）+ 厚集窗口限制长/短轨道命中次数。
- 作用机制：每条素数 l 的 Frobenius 类要么短（计数和被 2^{-s} 压制，`ShortOrdSq`/`ShortOrdLin`），
  要么长（厚集窗口 `WindowTwo` 排除），从而在选择中保住非零性。

### 段 3：θ-lift 链补「重数 m」

- `Formalism/ThetaLiftIndependence/Statement.lean`：`chainOp`（L24）、`chainOpM`（L52）、`thetaLiftAMF`（L80）。
- `m ≈ √X`：每次提升模拟一次重数，对应 remark.pdf 里 Claude 的关键一跳。
- **重要边界**：这一层只保证「能造出 m 重」以及良定义（按稳定子倒数 1/|stab| 加权），
  **不保证造出来的东西是真的**。防退化在最末端（段 4）。

### 段 4：√q 手工注入 + ℓ-adic 钉扎——「补一个特征」的核心

这是整个工程最直白的一处，也是对我们论点最硬的证据：

```lean
-- Development/.../AutomorphicForms/BlochKatoSelmerVanishes.lean:74
def algSat (n q : ℕ) (B : Multiset ℂˣ) : Multiset ℂ :=
  B.map fun α => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ)
```

**Weil 的 |α| = √q 不是从自同构推出来的，是手工乘进去的归一化因子。**

- `FrobEig`（同文件 L69）：惯性平凡 + charpoly(r σ⁻¹)|ι = ∏(X − b)，把 Frobenius 本征值钉在 `algSat` 上。
- `IsDivRep`（L83）：开稠密集上 Frobenius 特征多项式 = Satake 多项式。
- `DivAll`（L107）与 `PhiPol`（L43，`PhiPol.lean:14` 有 holds 证明）：WD 特征多项式 = satWD 多项式。
- `Formalism/LatticeSlopes/Statement.lean` 的 `SlopeInequality`：
  对 ℤ-格单射 φ : L ↪ M，`slope L ≤ muMax M + log C`——Bost 不等式给正性，防止链无限平延。

**这一层就是「在特征 0 里补一个特征」的字面实现**：用 ℓ-adic 表示 + Arakelov 斜率分析，
合成出「Frobenius 本征值被钉死」这个在正特征里由 σ 免费给出的性质。

### 段 5：局部-全局拼合 + 文献级块

- `Development/.../IntegralStructures/RowSrc.lean:6`：
  `galoisLocalGlobalStrong_recParameter = Row0b recT`，经 `PatchOneAlt.lean` 的 `PatchOne`/`OneTower`/`IsoOne`
  把 cofinite FrobEig 拼成整体表示。
- `Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7-11`：

  ```lean
  theorem everyCharacter_of_row (h : Row0b ...) : EveryCharacter :=
    LiteratureTheorems.every_character_of_literature_of_vWin
      ⟨h, Zero.LLC.recTExists, h⟩ (One.vwin_of_row h)
  theorem everyCharacter : EveryCharacter :=
    everyCharacter_of_row Gal.Int.galoisLocalGlobalStrong_recParameter
  ```

- `UpperTheory.LiteratureTheorems.OpenLiteratureStatements`
  （`.../EveryCharacterOfLiteratureOfVWin.lean:215-218`）只有三个字段：
  `caraianiLocalGlobalDual`、`localLanglandsExists`、`galoisRepOfPolarizedPairLit`，
  分别由 `h`、`recTExists`、`h` 提供。其后 `every_character_of_literature_of_vWin`
  展开一长串已形式化的文献结果（Deligne–Ribet、Bhatt–Scholze、Jacquet–Shalika、Serre…）。

- **判定**：这些文献结果在此仓库中被形式化为定理并接入，不是 `axiom`；
  但它们是**外部数学的账面搬入**——补课程的工作量在这里体现为「把现代朗兰兹全套翻译成 Lean」。

### 段 6：收尾——只用函数方程，不用 Landau

- `Formalism/GammaFactorNonvanishing/CritLine.lean`：`gammaFactor_ne_zero`（L5）、`critLine`（L10）、
  `rh_of_every`（L29）→ `Formalism.VW.rh_of_right`。
- 收尾只用 L 函数函数方程 + Gamma 因子非零；**没有 Landau 下界、没有显式公式**。
  （Landau 材料在 `Formalism/LandauZeroFreeBounds/`，只是中游输入。）
- 主入口 `Supplements/Kernels/MainTheorems.lean` 只有三行有效定理：
  `allChi := FinalTheorems.everyCharacter`、`rhOfAll := Formalism.VW.rh_of_every allChi`。

### 总表：有限域免费给的 vs 特征 0 里补的

| 正特征免费给出 | 特征 0 里的替代品 | 代码位置 |
|---|---|---|
| σ(x)=x^q 域自同构（幂映射即同态、有逆、典范唯一） | 2^k 单位群共轭类 + ℓ-adic Frob 类 | `BehrendSets/Statement.lean:9`、`FrobEig` |
| Weil 本征值模长 √q | **手工注入** `q^((n−1)/2)` | `BlochKatoSelmerVanishes.lean:74` |
| 交点数保证行列式非零 | Behrend 厚集 + B 进制展开唯一性 | `BehrendVariance/Select.lean` |
| 除子重数 m | θ-lift 链 m 次（m ≈ √X） | `ThetaLiftIndependence/Statement.lean` |
| 全局 Lefschetz 迹公式 | 局部-全局拼合 + 文献级结果 | `RowSrc.lean`、`MainConclusion.lean` |

**所以「有限域 → 无限域」的真相是：有限域从未被提升，它被拆解成五项功能，然后每一项被单独补造。**

---

## 二、特征连续统病态：他的工程反向确认了我们的诊断

我们的文献诊断（§四）列出连续统作为基座的三项结构缺陷。把它们和上面六段逐一对齐：

| 连续统病态（我们的诊断） | 精确含义（勘误后） | 他补的东西 | 补到什么程度 |
|---|---|---|---|
| 无算术强制的幂自同构 | char 0 中 x↦x^n (n>1) 不可加；复共轭虽是自同构但不是幂映射 | `OrdGrp`/`frob` 的 2-进类 + `FrobEig` | **替代了「阶/轨道长度」，没替代「幂映射即同态」** |
| 无唯一典范自同构 | Aut(ℂ) 有 2^ℵ₀ 野自同构，复共轭靠 ℂ 外解析结构挑出；Aut(GF(9)/GF(3))={id,σ} 定义即得 | Behrend 厚集 + 概率选择 `Select` | **程序化选出一个「够好」的集合，不是典范对象** |
| 无整性钉扎 | |α|=√q 不能从 ℂ 的自同构推出 | `algSat` 手工乘 √q + `PhiPol`/`DivAll`/`SlopeInequality` | **手工注入 + 解析不等式守住，不是结构自带** |

结论与你说的完全对齐：

> **他不是在特征 0 证明了什么新结构；他是在补一门课——把正特征里免费的三样东西，用 17.4 万行代码造出来。**

这三行里的「补到什么程度」栏尤其重要：三项都是**功能性替代**，没有一项恢复原生性。
我们的 `WeilRigidity.agda` 里 `t²+3s²=4q`、`α·conjᵉα=q` 是 σ 原生给出的 refl 事实，
不需要注入、不需要选择、不需要斜率分析——这正是两条路线真正的分工。

**诚实边界（必须保留）**：上述是结构诊断，不是对形式定理有效性的否定。
若全量构建通过且 `#print axioms` 干净，则「连续 RH 已被形式证明」在 Lean 标准下成立。
我们的价值主张应落在「原生侧的可计算性与 0-postulate」，而不是「他的证明不算数」。

---

## 三、两条路线的精确差异（更新版）

| 维度 | Alpöge / Claude | Sovereign GF(3^k) |
|---|---|---|
| Frobenius 来源 | 合成：2-进类 + ℓ-adic 类 + θ-lift 链 | 原生：σ(x)=x³，幂映射即同态，σ²=id |
| √q 来源 | **手工注入** `algSat` | 范数方程推出，`weil-norm-E1` refl |
| 重数来源 | θ-lift m 次（m≈√X），需 Rallis seesaw 保证与 Hecke 特征无关 | 扩域次数 k，Frobenius 迭代 σⁿ 天然给出 |
| 非零性来源 | Behrend 厚集 + 整数展开唯一性 + Bost 斜率 | `detNonzero↔bij` 有限组合事实 |
| 刚性代价 | 17.4 MB Lean + 全栈朗兰兹 + 文献搬入 | 0 postulate，穷举可判 |
| 覆盖范围 | ℂ 上连续 RH + 真 GRH | GF(3^k) 塔上的 Weil 结构实例 |
| 真实缺口 | 人不可读（25 万页 slop 未简化）；独立复核未完成 | **没跨出塔**：离散判据 ⇔ 连续零点线的字典是 `[ ]` |

**一句话**：我们不是他的「小规模版本」，我们是他的**输入侧**——他花 17.4 万行合成的东西，
我们在 GF(3^k) 上是 `refl`。差距不在基数，在**是否建了桥**。

### 条件二的三层升级（建议写入主文档）

原文「完备框架必须在特征 0 中显式构造出具备代数刚性的原生自同构」已被 Alpöge 的合成为例反证压力。
建议收窄为三条可独立判定的子条件：

- **(2a) 算术强制**：是否存在幂映射式自同构，或可证明等价的代理？
  —— 原生侧：是（σ）；他：部分（只有阶，没有幂映射同态）。
- **(2b) 整性钉扎**：|α|=√q 是从结构推出，还是手工注入？
  —— 原生侧：结构推出（refl）；他：手工注入 + 不等式守住。
- **(2c) 唯一典范**：选择是否依赖外部结构/文献假设？
  —— 原生侧：定义即得；他：概率选择 + 文献级块。

这样条件二不再能被「他造出了一个代理」一句话反证；它变成一张可以逐项打分的诊断表，
而我们的原生路线在 (2a)(2b)(2c) 三项上都能给出 refl 级见证。

---

## 四、我们路线的下一步（可执行）

### 立即：文档层（本周）

- [x] 本文档落库。
- [ ] `RH-GRH-三重完备性与离散闭合.md` §一条件二按 (2a)(2b)(2c) 收窄；
      保留「五大历史路线各自断裂」的结论，删除「连续宇宙整体不可证」的过度表述。
- [x] `Arithmetic/Riemann/README.md` 索引加入本文档。
- [ ] 对外第一屏加静态扫描表：postulate / hole / axiom / Float 计数（现有 RH 6 模块 1,017 行，全 0）。
- [ ] 措辞纪律：不写「q=3 是三个狭隘算例」（范畴错误，已入项目 MEMORY.md）；
      写「GF(3^k) 塔上 Weil 重数结构的 0-postulate 形式化」。

### 短期：Agda 形式化（1–2 周）

- [ ] **Frobenius 迭代 ↔ θ-lift 链的离散对译**。新建
      `src/Sovereign/Application/Problems/RH/FrobeniusChain.agda`，
      把 `RFH.agda` 的 t-递推 `t_{n+1} = t₁·tₙ − q·t_{n−1}` 重写成 σⁿ 迭代，
      证明每层 Hasse 界保持（q=3，n 可穷举）。
      ——这是「把 √X 次提升做成 n 次 Frobenius 迭代」的真正落点。
- [ ] **重数 m 的离散对应**：用 GF(3^k) 的扩域次数 k 当重数，证明「k 次提升 = Frobenius^k 的迹保持」。
- [ ] **√q 来源对照引理**：把 `weil-norm-E1` 的 `t²+3s²=4q` 与 Alpöge 的 `algSat` 手工注入并排形式化，
      作为 (2b) 判据的机器可读证据。

### 中期：对译字典（1–2 月）

- [ ] **路径 C 落地**：有限群特征和和界 `|Σχ(n)| ≤ √N·log N` 的离散版本，0-postulate。
      这是 Alpöge 的 Landau 型下界与我们的有限群特征和界真正结构呼应的地方。
- [ ] **离散判据 ⇔ 连续零点线双向字典**：这是对外宣称「离散 RH」的前提，也是目前最大的真实缺口。
      没有它，「离散主定理」即使证出也不能叫 RH。
- [ ] 若 Alpöge 构建 + `#print axioms` 核查通过，在文档中明确写：
      「合成 Frobenius 路线已成功；我们的价值在原生侧的可计算性，不在不可替代性。」

### 明确不碰

- 连续 RH / 真 GRH 的形式化竞赛（17.4 MB + 全栈朗兰兹，不是可追赶目标）。
- 用 q=3 的数值小否定塔的数学内容（GF(3^k) 的正当性来自 3 是奇素数、−1 非平方、存在 4 阶元 i，
  以及 12=3×4 的律学对齐，不来自「3 比 2 大」）。

---

## 五、证据附录（代码位置速查）

| 命题 / 结构 | 路径 | 行 / 符号 |
|---|---|---|
| ℚ 上 Frobenius 种子失败 | `Formalism/FrobeniusBaseCase/Statement.lean` | 174 `BaseCaseFalse` |
| 失败的真实证明 | `Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseFalseGeneralHolds.lean` | — |
| 有限域侧种子成立 | `Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean` | 86 `frobeniusSubstSpec` |
| 2^k Frobenius 类 | `Formalism/BehrendSets/Statement.lean` | 9–19 `OrdGrp`/`frob`/`OrdIff` |
| Behrend 厚集 | 同上 | 48–90 `BehrendFree`/`ThickSet`/`WindowTwo`/`OrbitOne` |
| 厚集选择（已证） | `Formalism/BehrendSets/BehrendVariance/Select.lean` → `TranslateMean.lean` | 11 `select : Select` |
| θ-lift 链 | `Formalism/ThetaLiftIndependence/Statement.lean` | 24 `chainOp` / 80 `thetaLiftAMF` |
| **√q 手工注入** | `Development/.../AutomorphicForms/BlochKatoSelmerVanishes.lean` | 74 `algSat` |
| Frobenius 本征值钉扎 | 同上 | 69 `FrobEig` / 83 `IsDivRep` / 107 `DivAll` / 43 `PhiPol` |
| Bost 斜率正性 | `Formalism/LatticeSlopes/Statement.lean` | `SlopeInequality` |
| 局部-全局拼合 | `Development/.../IntegralStructures/RowSrc.lean` | 6 `galoisLocalGlobalStrong_recParameter` |
| 文献级块 | `Development/.../ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean` | 215 `OpenLiteratureStatements` |
| 主结论 | `Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean` | 7–11 `everyCharacter` |
| RH 收尾 | `Formalism/GammaFactorNonvanishing/CritLine.lean` | 29 `rh_of_every` |
| 五定理入口 | `Supplements/Kernels/MainTheorems.lean` / `Main.lean` | — |

---

## 附录 A：工具全清单（通告 20 条时间线 + 代码目录对照）

> 来源：`https://alpo.ge/remark.pdf` 第 3–4 页的完整时间线（Claude 整理，作者自称部分为「slop 摘要」，以 Lean 为准），
> 与仓库实际目录逐一核对。日期为 2026 年。

### A.1 通告原文的 20 条时间线

| # | 日期 | 工具 / 步骤 | 作用 |
|---|---|---|---|
| 1 | 10/6 | **Stepanov 行列式** | 起点：函数域上带重数除子的行列式方法 |
| 2 | 10/9 | **CM 曲线上的不变导数 D**；惰性素数 p 满足 Dp≡0；D^a·θ(0)/Ω^a 的 p 整除性 | 算术强制的种子（「对整数求导」的替代尝试） |
| 3 | 10/19+ | **qN = Mᵏ + R 符号证明**（Weil/Deligne）；x₁x₂+…+x_{k−1}xₖ 型二次型；**GL5 六重覆盖上的 θ**；Poincaré 丛放在边上生成 θ | 无重数也能得到确定符号；N 的「自守性」 |
| 4 | 10/6+ | **W(1_S) ≥ 0 的行列式** | 再次解释为「重数 1 的 Stepanov」，bootstrap |
| 5 | 10/20 | **von Mangoldt Λ 加权和** Sχx；**Guinand–Weil 符号**；**Turán 方差测试函数**；Mehta 型扭族积分 | 把问题做成迹公式形状 |
| 6 | 10/8 | 测试函数 W(1₍₀,₁₎ + (~Xη)·1₍₀,₁/X₎) ≥ 0 | 给出 > 1−η |
| 7 | 10/14 | **GGP 周期**行列式；0/1 值对应交错权，或至多 m 个非交错权 | 周期进入行列式 |
| 8 | 11/15 | **全定酉群间迭代 θ-lift** U(X₀)→…→U(X_m)，π ↦ π ⊞ μⱼ[t] | **核心**：赢得重数 m，取 m ≈ √X |
| 9 | 11/15 | 提升的范数、层级、m 阶项抵消；**Chowla–Selberg / Weyl / Siegel 质量公式**给出可证整除性 | 控制整除性 |
| 10 | 11/15 | m 重迭代提升整除性的充分下界 | 保证不退化 |
| 11 | 10/6 | **Iwasawa 塔**（类比 F_{q^n}/F_q 上的鸽笼原理） | 有限域轨道结构的替代 |
| 12 | 11/15 | **Rallis seesaw**：迭代提升的周期是**与 Hecke 特征无关的 Bessel 周期** | 去掉周期对特征的依赖 |
| 13 | 10/6 | **Bost 斜率不等式** | 正性 / 高度控制 |
| 14 | 11/15 | 每次提升「代价」的精确计算；先验停在 2/3；主项与转移常数；需要「除法」 | 定量边界 |
| 15 | 11/15 | 跨 Hecke 特征 glue **积分结构**，构成「gcd」（额外平均） | 全局一致性 |
| 16 | 10/14 | **相对迹公式**；GL5 六重覆盖的自守性；Cauchy–Schwarz 归到 Poincaré 级数范数；积分结构列的近似正交 | 全局谱侧 |
| 17 | 11/15 | 对 twisting 杀不掉的上同调类 H¹(o_E[1/ℓ], ℚℓ/ℤℓ(−e))，争取 **Vandiver 的实质弱化**（K 群，Lichtenbaum） | 代数障碍清除 |
| 18 | 11/15 | 余体积、θ 级数指数、提升与形式的同余 | 定量收尾 |
| 19 | 10/19 | **Iwasawa 塔的精确选择：用 Behrend 集合** | 2-进塔的选择机制 |
| 20 | 11/16 | **GRH** | 结论 |

脚注另提到：Gabber 超曲面、Katz、Bertini、Bałaban 归纳、Borger 的 F₁ 类比、Ehrhart 猜想、Monge–Ampère、(2,3,6)-三角群技巧。

### A.2 按数学领域的工具归类（代码目录为证）

| 领域 | 工具 | 代码位置 |
|---|---|---|
| **算术几何** | Étale 上同调 | `Development/EtaleCohomology/` |
| | 奇点解消、blowup 范畴 | `Development/ResolutionOfSingularities/`、`.../BlowupCategories/` |
| | Abel 簇、CM 曲线、迹形式 | `Development/AbelianVarietyTheory/`、`.../CMTraceEmbeddings/`、`CMTraceForms/` |
| | 高度与 θ | `GroundTheory/HeightsAndTheta/` |
| | 晶体 / p-adic Hodge / formal group | `.../CrystallineRing/`、`Formalism/FormalGroupLog/`、`FormalGroupWitt/`、`WachModuleLifts/` |
| **自守表示论** | 迭代 θ-lift、θ 对应 | `Development/AutomorphicArithmetic/ThetaCorrespondence/`、`Formalism/ThetaLiftIndependence/` |
| | Rallis seesaw、Bessel 周期 | `Development/AutomorphicSpectrum/.../SeesawThetaDualPairStatement.lean`、`CompanionTheory/.../BesselParameterIntegrals/` |
| | 酉群质量公式、Siegel–Weil | `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/`、`Development/AutomorphicSpectrum/PublishedTheorems/SiegelWeil₂/` |
| | Harish-Chandra 模、离散序列、Pieri 规则 | `CompanionTheory/HarishChandraModules/`、`RealGroups/DiscreteSeries/`、`AutomorphicTheory/PieriRules/` |
| | Satake / 双 Weyl、Hecke 代数 | `Formalism/SatakeDualWeyl/`（含 `AdelicIwasawaHecke/` 60+ 文件） |
| | 相对迹公式、自守谱 | `Development/AutomorphicSpectrum/` |
| **解析数论** | von Mangoldt 和、零自由区、Landau | `Formalism/LandauZeroFreeBounds/`、`LFunctionBounds/`、`ZetaNonvanishing*/`、`GrowthSums/` |
| | Γ 因子、临界线收尾 | `Formalism/GammaFactorNonvanishing/` |
| | Dirichlet L / Dedekind L | `Development/AutomorphicArithmetic/DedekindLFunctions/`、`Formalism/DirichletDensity/` |
| **代数 / 格论 / 正性** | Bost 斜率、HN 滤过、逐次极小 | `Formalism/LatticeSlopes/`、`HarderNarasimhan/`、`SuccessiveMinima/`、`HermitianCurvature/` |
| | Behrend 集合、厚集选择 | `Formalism/BehrendSets/`（含 `BehrendVariance/`） |
| | Galois 上同调、Vandiver、Eisenstein 余核 | `Formalism/GaloisCohomology/`、`EisensteinCokernelLengths/` |
| | 局部-全局、互反律 | `Formalism/LocalToGlobal/`、`ReciprocityTheory/` |
| | 正性理论 | `PositivityTheory/`（449 文件） |
| **文献级搬入** | Deligne–Ribet、Bhatt–Scholze、global Artin reciprocity、Jacquet–Shalika、基变换等 | `.../EveryCharacterOfLiteratureOfVWin.lean:215` `OpenLiteratureStatements` 及其后数百条 |

### A.3 源码规模分布（.lean 文件数）

| 顶层模块 | 文件数 | 角色 |
|---|---:|---|
| `Development/` | 141,928 | 具体数学发展（自守算术、自守谱） |
| `Formalism/` | 18,254 | 抽象陈述骨架（140+ 子目录） |
| `GroundTheory/` | 8,507 | 高度、θ 等基础 |
| `ReciprocityTheory/` | 3,845 | 互反律、约化群 |
| `CompanionTheory/` | 2,027 | Harish-Chandra 模、谱几何 |
| `PositivityTheory/` | 449 | 正性输入 |
| `Lemmata/` | 167 | 通用引理 |
| `Supplements/` | 3 | 主定理内核 |
| `BuildAid/` | 5 | 构建辅助 |
| **合计** | **175,187** | — |

### A.4 诊断：工具分布如何印证「补课程」

把 A.1 的 20 步按本文的五项替换归类，可以看出工程的真实重心：

| 替换项 | 对应时间线步骤 | 工具数量感 |
|---|---|---|
| Frobenius 自同构 → 代理 | 2、3、8、11、12、19 | θ-lift 链、2-进塔、Behrend、seesaw |
| √q → 手工注入 | 9、10、13、15、17、18 | 质量公式、斜率、整除、上同调 |
| 交点数 → 非零性 | 1、4、6、7、16 | 行列式、GGP 周期、迹公式 |
| 除子重数 → θ-lift | 8、9、15 | 全定酉群迭代提升 |
| 迹公式 → 拼合 | 5、14、16、20 | Λ 加权和、代价计算、GRH |

**四项都指向同一件事：正特征里由 σ 一次给出的东西，在特征 0 里要拆成四组工具分别造。**
这正是本文第零节第 4 条「构造内容是补课程」的量化证据——不是形容，是代码行数与工具门类的分布事实。

---

## 创建日期

2026-11-21
