# Sovereign RH 构造主义路线：四阶段 Roadmap

> 哲学对立：**彻底构造主义 vs 极限逼近**。
> Alpöge 用 17.4 MB Lean + √X 链在特征 0 里**逼近** Frobenius 刚性；
> Sovereign 的路线是**由内向外、逐层扩展、最终在结构上反杀**：
> 不在特征 0 强行造 Frobenius，而在离散宇宙把原生 Frobenius 的 Weil 刚性推向极致，
> 并证明分析逼近的不可构造性。
> 前置诊断见同目录 `RH-GRH-合成Frobenius与代数刚性对译.md`，
> 技术字典见 `Frobenius迭代与Theta-lift链的离散对译.md`。

---

## 零、路线总纲与诚实边界

**这条路线不是「另一个 RH 证明」，而是「一个关于刚性来源的结构性论断」。**

- 主张范围：原生 Frobenius 在 GF(3^k) 上给出 0-postulate 的 Weil 刚性；
  特征 0 的合成链必须额外补造同等结构（√q 注入、ℓ-adic 钉扎、文献块）。
- **不可越过的边界**：「他的证明不合法」这种话在结构层面成立，
  在数学层面不成立。若 `lake build Main` 完成且 `#print axioms` 只含
  Lean 标准公理，则 Mathlib 官方陈述的 RH 就算形式证明成立。
  阶段三能证的是「**构造性内容提取的障碍**」，不是「证明造假」。
- 因此四阶段的真实产出排序：**阶段一/二是建设，阶段三是诊断，阶段四是记账**。

---

## 零·补、Alpöge Lean 仓库 `anyGeometry` 一手核验（2026-11-24 追加）

> **来源**：本机镜像 `/Users/zesheng/work/riemann-hypothesis-lean`（remote `CocoSgt/riemann-hypothesis-lean`，commit `7cbf7a0c3`）。
> 每条附文件与行号，可直接复核。**本节只记录一手事实，不改变「零」中的红线。**
> 外部转述（Nielsen 稿件、社交平台讨论）未读原文，不作依据。公开的验证记录见 F6，引文为抓取工具返回的逐字片段。

### 1. 事实

| # | 事实 | 位置 |
|---|---|---|
| F1 | `abbrev GeoP : Type 1 := ∀ D : D7, Core D → DivX D → Prop`。全库 `GeoP` 值的定义只有三个：实质性谓词 `geoOf`（`IsGeoOf` ∧ `HasTrueSurf`）、恒真谓词 `anyGeometry : GeoP := fun _ _ _ => True`、复合子 `geoCl` | `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:14,16-17,19`；同目录 `NotGeoClFalse.lean:26`；全库正则枚举 |
| F2 | `Main.lean` 的 import 传递闭包共 122,579 个模块；24 个使用 `anyGeometry` 的文件中 10 个在闭包内，最近的距 `Main` 为 6 跳 | 读各文件头部 `import` 行求传递闭包（未解析 `.olean`）；脚本 `import_closure.py`，2026-11-24 留存于 `/tmp/rh-audit/` |
| F3 | 几何谓词在闭包内有**两类**使用位置。族 / 包一侧用的是实质谓词：`AlgPkg (geoOf C K R)`、`ShimU D (geoOf C K R)`、`FormsPkg D (geoOf C K R)`、`ShimFam D (geoOf C K R)`（结构名照录，语义未逐一审读）。**除子一侧**（`OAt.geo` / `OX` / `geoCl`）的闭合实参只命中 `anyGeometry`（50 / 3 / 1 处）；`geoOf` 作 `OAt` 实参只出现在 `oAt_geoOf`，而它以 `IsGeoOf` 为前提 | `…/Definitions/AutomorphicMembership/FormsOver.lean:57,94,101,105`；`…/Definitions/AutomorphicMembership/NotLamAreShift.lean:152-161`；闭包内正则计数 |
| F4 | `divEx_prov (𝒮) (hOx : 𝒮.Ox = OX anyGeometry) : DivEx 𝒮`：除子 Y 由 `exists_divT` 构造，Y 的 `geo` 字段用 `trivial` 填 | `…/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean:204-209` |
| F5 | `riemannHypothesis : RiemannHypothesis := rhOfAll` 无前提；仓库内无 `RiemannHypothesis` / `riemannZeta` 的重定义；Mathlib pin 为官方仓库 `0df444a3` | `src/Main.lean:4`；全库正则搜索；`lake-manifest.json` |
| F6 | **形式证明已通过多重独立验证**：全部 175,187 个模块零错误编译；沙箱内独立 `lake build`「exit 0, zero errors」，导出「byte-identical to the published one」；五条主定理只依赖「propext, Classical.choice, Quot.sound only」；Lean 官方内核、con-leche / con-ron、nanoda、lean4lean 等接受全部导出或全部模块；两件比较工具确认所证命题「is exactly Mathlib's statement of the Riemann Hypothesis」 | Lean FRO 与 Mathlib Initiative 联合声明（2026-11-21）：`leanprover-community.github.io/blog/posts/riemann-hypothesis`；A. Sutherland 验证日志（更新于 2026-11-24）：`math.mit.edu/~drew/grh` |
| F7 | 本库静态扫描：`axiom` / `sorry` / `sorryAx` / `native_decide` / `skipKernelTC` 均 0 命中；仅 2 处 `partial def`（元编程辅助，`MetaM` / `Environment` 层）与 2 处 `addDecl`（复制既有声明，仍过内核） | 全库正则扫描；`Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean:41,78,82`；`Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean:18` |
| F8 | 本机曾有一次 `lake build`（2026-11-22 17:06 至 11-24 12:36，由另一工具的会话启动），至停止时约 29,900 个 `.olean`，`Main.olean` 从未生成。它是冗余重建，已于 2026-11-24 停止，`.lake/build` 已删除（释放约 210 GB）；`.lake/packages` 与源码保留。判断 lake 构建是否完成只看 `Main.olean` 是否存在与日志末尾的 `EXIT=` 标记——`[done/total]` 只统计已排队任务，不是完成度（本次该比值一度显示 99.7%，实际完成 2%） | 进程表；`df` |

### 2. 这组事实意味着什么、不意味着什么

- **意味着**：除子一侧名为「几何」的槽位没有实质内容。F4 里 `trivial` 填的是除子的几何来源证书，不是除子本身。它是审稿时追问「除子的正性究竟从哪里来」的线索。
- **不意味着实质几何在主链上缺席**。F3 前半句恰相反：族 / 包一侧用的是 `geoOf`。
- **不意味着主定理空真或不成立**。按 F6，形式证明已通过多重独立验证：Mathlib 定义的 `RiemannHypothesis` 是 Lean 类型论加三条标准公理的定理，`anyGeometry` 改变不了这一点。空真来自假前提，`True` 作前提不产生空真。它去掉一项要求，而不是预设一项前提：全库 0 处 `axiom`、0 处 `sorry`（F7），主定理签名无假设。
- **不意味着动机**。代码里没有注释解释 `anyGeometry`。「特征 0 几何正性不可判定所以被迫设 `True`」是推测，且代数数的正性本就可判定。
- **import 距离不等于证明依赖**。F2 / F3 只说明文件在依赖闭包内，未确认每条使用 `anyGeometry` 的定理都出现在最终证明项里；主定理对除子一侧是否需要实质几何，未判定。[未验证·路线推测]
- **不等于「坐实 Nielsen」**。Nielsen 稿件的论证内容未读原文；成立的只有 F1–F6。

### 3. 结论与仍然开放的问题

- 「零」中那条红线的前提**已经满足**（F6）：`lake build` 完成且公理干净。**Mathlib 官方陈述的 RH 算形式证明成立。** 任何「Alpöge 的证明空真 / 循环 / 不合法」的表述与本节事实相抵触，不得写入本目录文档。
- 仍然开放的是**理解**，不是真假。联合声明把「explain the new ideas in this proof」列为对社区的期待。`anyGeometry` 是一条具体线索：除子一侧为何不需要实质几何。[未验证·路线推测]
- 验证日志自述的边界（逐字片段）：「A passing check shows that the formal statements, as written in Lean against Mathlib's definitions, follow from the three standard axioms」——即结论依赖所用内核，以及 Mathlib 定义符合其本意。所核对的 GRH 只限 Dirichlet L 函数（据页面摘要）。
- 本机那次重建（F8）不影响上述结论，已于 2026-11-24 停止并删除 `.lake/build`。

### 4. Agda 侧对照（同一把尺子）

2026-11-24 本机（`~/.local/bin/agda`，Agda 2.9.0）逐模块类型检查：

| 模块 | 结果 | 证明的内容 |
|---|---|---|
| `WeilRigidity` / `RH` / `WeilRH` / `ZetaDiscrete` / `ZetaFunctional` / `FrobeniusBlind` | exit=0 | E₁ / E₂ / E₆ 在 F₃、F₉ 的实例数值、递推序列与常量；**不是一般定理** |
| `NoNormT0Even`（未提交） | 修复后 exit=0（重名重构后复检仍为 0） | `∀ m s → s·s ≢ 4·3^(2m+1)` 与 `∀ m s:ℤ → 3s² ≠ 4·3^(2m+2)`。相邻的可解情形（n 奇、t=0、s=±6）在同一套定义下由 `refl` 成立，故「偶指数无解」是数论事实而非定义缺陷 |

- 仓库内没有 `witness` 函数、超奇异、Waterhouse 分类、自同态环（后三项见 `Weil刚性路径可行性审计-九项清单.md` 第 8 项）。
- **类型检查通过只说明项是良构的，不说明内容实质**。同一条线上存在「名称多于内容」的项，引用时**不得当作定理**（按散文断言规则属 (b)，无对应定理）：
  `BSD/BSD.agda:91` `hasse-ok : 0 ≡ 0`、`RH/FrobeniusBlind.agda:67` `det-J-formal-frob : ∀ p → T₁ ≡ T₁`、`RH/RH.agda:70` `func-sig : N₀ * q3 ≡ N₂`（即 1·3 ≡ 3）。
- `RH/ZetaDiscrete.agda:55,61` 头注「编译器的判决：连续 RH 不可证」：模块体只有常量，该断言无任何定理支撑，属 (b)。[直觉·未验证] 且与 F6 直接相抵触——Mathlib 的 ℂ 上已有通过多重独立验证的 RH 形式证明——**应撤回**（2026-11-24 尚未改动该文件）。
- `RH/WeilRigidity.agda` 头注与尾部注释曾称 ℤ[ω] 的共轭与 GF(9) 的 Frobenius σ(x)=x³「同构」：无对应定理，且与下述手算矛盾 [未形式化]：特征 3 下 x²+x+1=(x−1)²，故 ℤ[ω]⊗𝔽₃ ≅ 𝔽₃[ε]/ε² 不是域；约化后得到 GF(9) 的是 ℤ[i]。**2026-11-24 已在该文件内勘误**（头部、尾部两处，仅改注释，exit=0）。
- `NoNormT0Even` 的重名处理：其 44 个顶层声明中原有 23 个与库内其他模块同名（`⊥` / `¬` / `cong` / `sym` / `trans` / `+-comm` / `*-comm` / `pow3` / `tri` 等）。2026-11-24 已把辅助层整体移入子模块 `NoNormPrelude` 且不重导出，顶层只剩三条主定理与 ℤ 层；标识符未改，仅加缩进。外部探针确认：只 import 时 `cong` 为 `NotInScope`。重复检查门禁是否接受这种结构 [未验证·路线推测：本机无法运行该门禁；核实动作 = 在部署了 math-proof preset 的机器上 `git add` 后运行 `engineering/check_duplicate.sh`]
- 阶段四「22 万行从未经过类型检查」是 2026-11-21 的状态。2026-11-24 本机已能逐模块检查（见上表）；**全库门禁未在本机重跑**：`~/.dsh`（`proof_dag`、`gates.mjs`）与 `.git/hooks/pre-commit` 在本机不存在。

---

## 阶段一：纵向延伸 —— 从特例到有限域塔的全称量化

**现状核查**：递推层已参数化（`BSD_L3.agda` 的 `t-rec : ℤ → ℤ → ℕ → ℤ`），
刚性层未参数化（`WeilRigidity.agda` 的 `weil-norm-E1/E2/E6` 是 q=3 的 refl 实例，
`q3` 在 RH/BSD 轨道出现 109 次）。

| 项 | 内容 |
|---|---|
| 目标 | `∀ (p : Prime) (k : ℕ)` 的 Frobenius 迭代塔，重数退化为代数次数 n |
| 已有基础 | `FieldTower/` 36 件 13,584 行（GF9→GF729）；`t-rec` 参数化；`Eisenstein` 环 918 行 |
| 核心工作 | 把 `weil-norm-E1` 提升为一般命题：`∃ s d, (t-rec q t1 n)² + d s² = 4 q^(n+1)` |
| **真实难点** | `d=3` 写死在 `Eisenstein.agda:647` 的 `normᵉ (eis a b) = a²−ab+b²`（判别式 −3）。推广到任意 p 要换 `ℤ[√−d]`，类数 ≠ 1 时唯一分解失效。**不是加一个 `∀ p k` 就能解决** |
| 判据 | 一个不依赖 q3 常量的参数化定理，Agda 0 postulate 通过 |
| 难度 | 中高（代数数论障碍，非工程障碍） |

---

## 阶段二：横向扩展 —— 从曲线到高维簇的离散化

**现状核查**：`Application/Geometry/Sheaf.agda` 的 `Presheaf` 只有 `ℱ-dim` 一个字段，
`restrict` 在注释里写明「需 Functor 范畴，~500 行」；`Variety.agda` 35 行只做 ℙ¹=10、ℙ²=91 点数；
`Synthesis/Geometry/ChernClass.agda` 的 `TransportPolar/Toroidal` 都是恒等映射。
**Deligne 级的高维 Weil RH 在本库里一行都不存在。**

| 项 | 内容 |
|---|---|
| 目标 | 有限域上任意维簇的 Weil 刚性，用有限矩阵特征多项式范数方程替代 p-adic 分析 |
| 路线 A（重装备） | 离散 étale 上同调 + Lefschetz 迹公式——需从零建范畴论层论，千行级 |
| 路线 B（绕过） | 组合/有限矩阵法：把 Frobenius 作用在有限生成模上，特征多项式系数整数化；对**曲线**已有 Hasse 初等证明可推广，对**高维**无已知的纯组合证明（这恰是 Deligne 1974 的 Fields 工作） |
| **真实难点** | 「无需上同调的一般 Weil RH」目前**不是已知定理**。阶段二不是工程任务，是研究任务 |
| 建议裁剪 | 先做 q=3 上 **曲面**（ℙ² 已有 91 点计数）的显式点计数与 |α|=√q 的矩阵核对；不碰一般簇 |
| 难度 | **最高（全路线瓶颈）** |

---

## 阶段三：直击要害 —— 构造性证明「合成链条的不可逆扭曲」

> 这是用户 Roadmap 里最有杀伤力的一步，也是**前提最需要审查**的一步。

**原始命题**：任何从特征 0 合成 θ-lift 链无损映射到 `ℤ[ω]` 范数方程的尝试，
都会因分母非单位或选择公理的非构造性而断裂。

**核查结论（必须诚实写出）**：

1. **选择公理论点站不住**。Lean 侧 `Classical.choice` 出现在 23,535 个文件（13%），
   但 `Main.lean` / `MainTheorems.lean` / `MainTheoremsAll.lean` 三件主入口计数为 **0**。
   Lean 的标准公理（choice/quotient/propext）在 Lean 社区**不算「无公理」违约**——
   Mathlib 全库都建立在其上。因此「他用选择公理 ⇒ 权威破产」在社区标准下不成立。
   可证的版本只能是：**他的证明无法在构造性元理论中提取出计算内容**，
   这是一个关于 proof 的元命题，需要独立证明，不是现成结论。
2. **分母非单位论点可能成立但需具体化**。`algSat n q B` 乘的是 `q^((n-1)/2)`；
   q=p 为素数时这不是 `ℤ[ω]` 的单位（范数 q ≠ 1）。要证「链条在某步必须走出
   `ℤ[ω]`」，需先定义「离散影子链」的形式——目前代码里没有这个对象。
3. **可操作的弱版本**（建议作为阶段三的实际目标）：
   在 Agda 中证明一个**不可穿透引理**——若要求 θ-lift 链的每个中间态都落在
   `ℤ[ω]` 且保持 `normᵉ` 乘法性（`Eisenstein.agda:906` 已有 `norm-mul`），
   则中间态数 m 必须 ≤ 1；m ≥ 2 时某个中间范数不是 `ℤ[ω]` 的范数。
   这是一个**有限的、可证伪的、0-postulate 的**命题，且直接命中
   「√q 是外挂」这一结构差异。

| 项 | 内容 |
|---|---|
| 目标（弱版本） | 上述不可穿透引理 |
| 意义 | 不是「废掉他的证明」，而是**证明构造性提取存在结构障碍** |
| 判据 | 引理在 Agda 中 0 postulate 通过；明确声明它不否定经典正确性 |
| 难度 | 中（需先定义影子链，命题本身可在 Eisenstein 环内穷举） |

**红线**：不得对外表述为「Alpöge 的证明依赖选择公理所以无效」。这是范畴错误，
会在第一次同行评审中被击穿。正确表述是「构造性内容提取的障碍」。

---

## 阶段四：形式化闭环 —— 0 公理验证

**现状核查**：全库真实顶层 `postulate` 仅 1 文件
（`Synthesis/Model/DiscreteCCHM.agda` 两条：`discreteGlue`/`discreteCanonicity`），
真实洞 0 个；RH/BSD/FieldTower/Langlands/Geometry 目标目录全部干净。
`Classical.choice` 全库 **0 处**。

**但真正的闭环缺口是编译器**：本机 Agda 2.9.0 在
`/Users/zesheng/Downloads/agda`（带 Safari quarantine），四个依赖库
（standard-library-2.4 / cubical-0.9 / agda-categories / agda-algebras）一个没装，
全库 0 个 `.agdai`。**22 万行从未经过类型检查**。

| 项 | 内容 |
|---|---|
| 前置 | 装库 + 写 `~/.agda/libraries` + 跑通单文件 + 全库类型检查 |
| 目标 | `WeilRigidity` 主定理带 0 postulate / 0 axiom 标签 |
| 判据 | Agda 类型检查器实际通过；`#print axioms` 等价物为空 |
| 难度 | 工程量大但无数学障碍 |

---

## 全局难度排序（回答用户提问）

| 阶段 | 难度 | 性质 | 理由 |
|---|---|---|---|
| **阶段二**（高维簇） | **最高** | 研究级 | 一般 Weil RH 的纯组合证明不存在；Sheaf 仅一字段，距 étale 上同调千行以上 |
| 阶段一（∀ p k） | 中高 | 代数数论障碍 | t-rec 已参数化，但判别式 −3 写死、`ℤ[√−d]` 类数问题未解 |
| 阶段三（反杀） | 中 | 需重述命题 | 原始「选择公理」论点站不住；弱版本（不可穿透引理）可在 Eisenstein 环内做 |
| 阶段四（0 公理） | 中低 | 工程 | 代码纪律已达标，缺的是编译器和库 |

**一句话**：**最难的既不是「反杀」也不是「参数化」，而是阶段二的横向扩展**——
因为那一步要求的是 Deligne 级别的新数学，而不是现有代码的更大规模实例化。
阶段三看起来最野心勃勃，但只要把命题从「废掉经典证明」收窄为
「构造性提取的结构障碍」，它反而是四个阶段里最可完成的。

---

## 创建日期

2026-11-21
