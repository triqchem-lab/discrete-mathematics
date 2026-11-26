# OpenAI ω = 9/4：证明阅读记录（2026-11-26）

> 接续 `OpenAI-omega-9-4-只读审计-2026-11-25.md`。那一轮读完的是**陈述层与结构层**；
> 本轮按用户指示「读证明」：通读论文正文，并沿 Lean 证明的主干逐环读下去。
> **阅读不是内核检查**：本轮没有运行构建，也没有运行 Comparator（沿用「默认通过」的指示）。
> 凡是我在这里写的「成立 / 一致」，都只是**读到的内容**，可靠性仍由 Lean 内核与 Comparator 负责。

## 一、覆盖面（如实）

### 论文
`preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/build/`
共 28 个 `.tex` + 1 个 `.bib`，7,415 行。

| 状态 | 文件 | 行数 |
|---|---|---|
| 逐行读完（24 件） | intro 266、obstruction 186、consequences 81、background 99、list 205、prices 366、valued 330、motion 435、boundary 211、contact 720、sync 246、fermions 270、sphere 355、incidence 211、sorting 954、lookup 60、local 367、local-plant 293、local-motion 226、rounds 366、core-width 375、round-iteration 127、assembly 337、shaving 128 | 7,214 |
| 只读了结构 | main.tex、README.md | — |
| 没读 | history.tex（史料小节，60 行）、style.tex、locators.tex（宏） | — |

### Lean（`OAI/LinearAlgebra/MatrixExponent/`，555 件 263,011 行；`SpectralBooks/`，840 件 85,587 行）

| 深度 | 文件 |
|---|---|
| **全文读完**（26 件） | SpectralBooks: ExactExponent 65、SquareRankModel 56。MatrixExponent 直属: FieldFormula 24、RationalCircuits 53、Realization 22、Obstruction 32、Rectangle 103、Iteration 164、ListBounds 34、Specialization 118、RankCriterion 80、Bilinearize 130、FieldExtension 131、Network 96。Integral: Model 43、RingFormula 17。Prices: Sync 53。Rounds: Installation 25、Install 178、Compression 93。Processor: Resistance 71。Diagonal: Bounds 36。Shaving: Defs 61。Tagged: Hard 16。Sphere: General/Law 33、General/Local 40 |
| **读了关键段**（陈述 + 顶层证明） | Valued/Shared（300–345、520–609）、Routing/Dual（317–366）、Rectangle/Rows（355–420）、Rectangle/Face/Contact（提纲 + 228–275）、Shaving/Network（318–379）、Diagonal/Broadcast（800–867）、Tagged/Reduction（提纲）、Prices/Motion/{Rigidity,Tripod}（`Moving.limit`、`Leaves.contact`）、Routing/{GeometryTerms,GeometryComparison}、Prices/{Chord,Space}、BatchDescent/{Compilation,Encoded}（头注与主定理）、Processor/{DispatchSize}（`Programmable`/`ControlBound`） |
| **只读了陈述或头注** | 其余各目录的入口定理与模块标题 |
| **没读** | 约 25 万行的内部证明：Sphere/Assembly/Routing/Packing/Processor/BatchDescent/Prices/Valued/Rounds 的组合与分析细节；上界机器（`Upper/`、`Integral/Upper/`、`MatrixMultiplication`）；`TensorSpectrum` 的传递闭包 |

## 二、证明的结构（论文 ↔ Lean 对照）

「Lean 位置」给文件:行。**核对深度**分三档，务必按档理解：
「陈述已读」= 我读了 Lean 陈述并与论文陈述对过；「按名称」= 只凭名字与用法对应，陈述没读；「仅目录」= 只到目录。

| 论文 | Lean | 核对深度 |
|---|---|---|
| 定理 1.1 `thm:square`（每域 ω = 9/4） | `SpectralBooks/ExactExponent.lean:11` `square_exponent` := `(formalOmega_square_eq_omega F).trans (omega_eq F)` | 陈述已读 |
| 定理 1.2 `thm:shaving`（张量幂的压缩） | `Shaving/Defs.lean:22` `Compresses`（头注自述「Theorem 2.1 的结论」）；证明 `Shaving/Network.lean:342` `compresses_of_stages` | 陈述已读 |
| 引理 `lem:macro`（一次压缩） | `Rounds/Install.lean:144` `Installable`；`Shaving/Defs.lean:39` `ArityStep`（头注「第 5 节表网络引理的一次应用」） | 陈述已读 |
| 引理 `lem:batch-table`（批量查表） | `Lookup/Network.lean:58` `lookup_network` | 按名称 |
| 定理 1.3 `thm:many`（列表互异性的体积） | `Tagged/Hard.lean:11` `Tagged.Hard`；入口 `BatchDescent/Hard.lean:17` `hard` | 陈述已读 |
| 命题 `prop:finitefield`（有限域上 ω ≥ 9/4） | `Rectangle.lean:85` `of_prime_fields` + `Obstruction.lean:19` `contact_of_network_estimates` | 陈述已读（证明全文） |
| 引理 `lem:bilinearize`（q 个非标量门 ⟹ 秩 ≤ 2q） | `Bilinearize.lean:111` | 陈述已读（证明全文） |
| 引理 `lem:specialize`（有限专门化） | `RankCriterion.lean:74` `finite_specialization`；`Specialization.lean:89` `specializeRank` | 陈述已读（证明全文） |
| 定理 `thm:extension`（价格扩张 + 乘积检验） | `Prices/Tensor.lean:507` `extension_iff`、`:529` `assisted_extension_iff` | 按名称 |
| 定理 `thm:gauss`（Gauss 提升） | `Valued/Shared.lean:63` `exists_lift` | 按名称 |
| 引理 `lem:star`（星形不等式） | `Valued/Shared.lean:389` `value_star` | 陈述已读 |
| 定理 `thm:motion`（运动的刚性） | `Prices/Motion/Rigidity.lean:91` `structure Leaves`、`:773` `Moving.limit`；`Prices/Motion/Tripod.lean:549` `Leaves.contact` | 陈述已读 |
| 命题 `prop:tripod`（三脚架原理） | `Rectangle/Rows.lean:363` `Propagation`；`Rectangle/Face/Contact.lean:98` `diagonal`、`:253` `propagation_of_tripod`、`:262` `propagation_of_potential` | 陈述已读 |
| 定理 `thm:sync`（同步） | `Prices/Sync.lean:31` `Synchronization`；`Valued/Shared.lean:486` `diskSync_of_collapse`、`:268` `sharedPrice_of_disk` | 定义已读；两条定理按名称 |
| 推论 `cor:sharedprice`（同时定价） | `Prices/Sync.lean:19` `SharedPrice`、`:40` `Synchronization.sharedPrice` | 陈述已读（文件全文） |
| — （二分） | `Valued/Shared.lean:573` `contact_of_not_shared`（无限可数域）、`:593`（有限域）、`:603` `shared_of_saving`；`Rectangle/Rows.lean:393` `rigidity_of_contact` | 陈述已读（证明全文） |
| 定理 `thm:incidence`（关联不等式） | `Routing/GeometryJets.lean:250` `incidence_bound`、`Routing/PartitionsPlane.lean:736` `affine_incidence` | 按名称 |
| 定理 `thm:sort`（条件稳定排序） | `Routing/Dual.lean:319` `sorting_of_shared_price`（`∃ p, 1 < p ∧ p < 2 ∧ Lookup.Sorting F p`）；`Lookup/Defs.lean:55` | 陈述已读 |
| 引理 `lem:local`（局域集中） | `Rounds/Local.lean:88` `LocalLaw`；`Sphere/Panel/Wave.lean:169` `local_law` | 按名称 |
| 引理 `lem:core-width`（核宽度缩减） | `Rounds/Contraction/{Beat,Reset}/` | 仅目录 |
| 引理 `lem:fixed-transcript`（实现转录） | `Assembly/`（`Finishes`、`Transforms`） | 仅目录 |
| 背景：CAT(0) 比较 | `Prices/Motion/ScaleSlope.lean:154` `SpectralComparison`；**定理** `Routing/GeometryComparison.lean:689` `spectralComparison` | 陈述已读；证明读了 |
| 背景：严格谱比较 | `Spectrum/Comparison.lean:215` `strictComparison` | 按名称 |

## 三、各部分的证明手法（读后的一句话概括）

- **`obstruction.tex`（枢纽）**：列表互异性有排序网络作上界（尺寸 O(n_w w²)）；若 ω_k < 9/4，则反复压缩把每个输入比特的代价压到 O(w^η)，与硬度 w^σ（η < σ）矛盾。
- **`list.tex`（硬度）**：两次互异性检测实现带标签置换 `Tag(h,h)`。论文分两种情形：无端口域用价格不等式 + 图熵界（Ω(r√(log q))）；有端口的有限域用电路下界论文的带符号计数张量的批量下界 + 带标签置换的「下降」。
- **Part I（价格几何）**：赋值域上的价格、辅助代价、价格扩张定理（凹齐次函数的支撑超平面 + 紧性）；Gauss 提升；星形不等式（整系数插值 + 中国剩余定理）。运动定理：在位移开始的深度重标度、取超极限得到「圆盘树」，四等枝顶端的公共标签率 ≤ 3/2。三脚架原理：多项式乘法价格的连续轮廓、能量泛函与径向收缩、三个方向积分的比较、强极小值原理（Fatou）。同步定理：极小化站点不能移动，否则与运动定理矛盾。球张量的价格：加权重心的能量。
- **Part II（排序）**：两条关联不等式 → 短地址集上的置换（坐标分解、边染色）→ 均匀位移引理（Garland 链接能量论证，C₀ = 100）→ 有限检测（超极限构造群作用）→ 路由协议（检验失败的球上用严格谱比较得到路由恒等式）→ 递归 + 基数排序得 p = 2 − 1/(2a)。
- **Part III（局域集中）**：自由费米子定义球张量（Pfaffian；融合命题；维数 ≤ e^(π√(h/3))；融合宽度引理）。每个胞腔两个球形式（缝合球 A、私有球 B）；缝处的转置恒等式；用 P¹ 上除子次数论证从碰撞系数重构取值；越缝一次缝能量下降至少 μ。
- **Part IV（体积）**：各轮先集中平方入射度（预算 Σ入射度² = O(WT)），再用「拍」缩短核线（六方三角排列的接线恒等式给出 λ < 2；厚/薄染色；转子重置度数，混合由随机可逆二元矩阵控制）。装配：把「和项 + 终端线赋值」编码成转录，固定程序局部核对，消息排序匹配。最后 `shaving.tex` 选参数（δ ≤ 1/10、J 步、γ = Δ/2）得到定理 1.2。

## 四、发现

### 4.1 挑战件的定义与库内原件逐字相同（机械化核对）
`lean/ComparatorChallenges/MatrixExponent.lean` 只 import Mathlib，自带一套定义。用脚本把它的每个定义块（去空白后）在库内全部文本里查找：
**15/15 逐字相同**（`Gate`、`Program`、`MatrixAlgorithm`、三个 `cost`、`gatePolynomial`、`registerPolynomial`、`FormalCorrect`、
`wireDimension`、`FormalAdmissibleExponent`、`formalOmega`、`dualExponent`、`formalAlpha`；库内原件在
`MatrixMultiplication/Model.lean`、`SpectralBooks/{FormalCircuit,Scaling,ArithmeticExponent,Elongated,DualExponent}.lean`）。
所以 Comparator 核对的那句话与库里证的定理字面相同。
**Comparator 本身是外部工具**（`github.com/leanprover/comparator`，见 `lean/ComparatorChallenges/README.md`），其源码本轮没有审。
映射 `ComparatorChallenges/MatrixExponent.json`：`solution_module = OAI.LinearAlgebra.SpectralBooks.ExactExponent`；
`permitted_axioms = propext, Quot.sound, Classical.choice`；`enable_nanoda = False`。

### 4.2 Lean 的陈述强于论文
- 论文只陈述 `1/2 ≤ α_F ≤ 2/3`（`intro.tex:83`、`consequences.tex:79–80`）；Lean 证 `dual_exponent : formalAlpha F = 1/2`（`ExactExponent.lean:15`）与矩形闭式（`:50`）。
- Lean 另证：任意非零交换环上的无除法指数（`Integral/RingFormula.lean:8` `exponent_eq`、`:13` `square_exponent`）；
  严格**对偶**节省也给出共享价格与排序（`Valued/Shared.lean:581` `shared_of_dual`、`Routing/Dual.lean`）。

### 4.3 Lean 的硬度证明路线与论文不同
论文 `list.tex` 分「无端口 / 有端口」两种情形，并引用配套论文 [oaP] 的批量下界与 [oaG] 的下降。
Lean 只有一条路线，对一切有限域：`Diagonal.Resists`（`Diagonal/Bounds.lean:12`，即批量下界）在库内**由对角化证出**
（`Diagonal/Broadcast.lean:813` `resists_of_programmable`：拟线性通用处理器模拟小的批量实现并在自己的编码处翻转答案），
配合 `Diagonal.Descent`（`Bounds.lean:23`）得 `Tagged.Hard`（`Broadcast.lean:556` `hard_of_resists`）。
`Processor/Resistance.lean` 头注写明「控制器及其尺寸界不需要任何复杂性假设」。
即：论文的「无端口」情形（图熵）在 Lean 里不需要。**这是差异，不是矛盾**——两边证的是同一个定理。

### 4.4 CAT(0) 不等式在 Lean 里是定理
论文把谱空间嵌入完备 CAT(0) 空间当作配套论文 [oaG] 的输入。下界子树**没有 import 任何几何库**；
它把 CAT(0) 四边形比较写成谓词 `SpectralComparison K`（`Prices/Motion/ScaleSlope.lean:154`），
并在 `Routing/GeometryComparison.lean:689` 对一切域证出（在测地项的有限度量空间上用中点与 Busemann 单调性）。

### 4.5 外部依赖（下界子树的全部非 Mathlib import）
- `OAI.LinearAlgebra.TensorSpectrum.*`：11 个模块，合计 1,487 行，都是初等引理件
  （`Additive/Catalyst`、`Additive/RankAnalysis`、`AdditiveCone/Encoding`、`CharacterPower`、`GrowthRow`、
  `Multiplicative/Character`、`SeparationWeights`、`TagEntropy`、`TagGrowth`、`TagOptimized`、`TagWords`）。
  被谁引用：`Spectrum/Comparison.lean`（谱比较）、`Spectral/Transport.lean`、`Prices/Fields.lean`、`Valued/StarWeights.lean`、`Coefficients.lean`、
  `Rectangle/{Border,Interior,Multi,Rows,Sparse,Dual}.lean`、`Upper/` 与 `Integral/Upper/`（字符幂、标签熵、标签词、分离权重）。
- `OAI.LinearAlgebra.MatrixMultiplication.*`：4 个模块（ℂ 上上界机器），被 `Upper/`、`Integral/Upper/`、`Integral/UpperBound.lean`、`Coefficients.lean`、`LocalTensor.lean` 引用。
- 这 11 个模块自己的传递闭包没有追。

### 4.6 逃生口扫描（`MatrixExponent/` 555 件；`SpectralBooks/` 840 件）
`sorry` 0、`axiom` 0、`native_decide` 0、`sorryAx` 0、`skipKernelTC` 0、`unsafe` 0、`implemented_by` 0、`@[extern]` 0、`opaque` 0、`partial def` 0。
`admit` 字样各 5 处，全是散文（如「admit all required sorting tables」），不是策略。
`set_option maxHeartbeats` 15 / 16 处（只是超时选项；两处 `admit` 均已逐行看过，都是文档字符串里的英文单词）。
`Classical.choice` 52 / 24 处（在允许公理表内）。
声明计数（MatrixExponent）：定理 13,161、定义 6,834、缩写 2,364、结构 559。

## 五、这份阅读确立了什么、没有确立什么

**确立了**（都是读到的内容，不是机检结果）：
1. 论文是一篇连贯的、研究论文级别的完整论证：每个定理都有证明，每个证明都指明了所用的引理。
2. Lean 的主干与论文逐条对应（§二的表），陈述的参数（δ ≤ 1/10、m ≤ n^1.1、e ≤ m·h^(−2a)、1 < p < 2、d ≤ n^κ）两边一致。
3. 我读过的 Lean 顶层证明都是真实的证明，不是循环引用或空转。
4. 挑战件的陈述与库内定理字面相同。

**没有确立**：
1. **内核检查**。我没有运行构建，也没有运行 Comparator。
2. **约 25 万行 Lean 内部证明的正确性**。我只读了主干；组合与分析细节没有读。
3. **论文各步骤的数学正确性**。读的时候没有发现结构性矛盾，但阅读不能代替核对。
   依我的阅读，最需要仔细核对的是：`motion.tex` 的阈值重标度与超极限、`contact.tex` 的强极小值原理、
   `sorting.tex` 的有限检测（超极限构造群作用）、`core-width.tex` 的混合步骤。这是 [阅读判断]，不是发现错误。
4. **Comparator 工具**与 **`TensorSpectrum` 的传递闭包**。

## 六、过程记录（本轮的失误与更正）
- 取伴随模块时我写了 `rg -oh …`：`-h` 是「帮助」而不是「不显示文件名」，结果把 rg 的帮助文本当成路径清单，
  后台脚本向一个新建目录写了 311 个 GitHub 的 404/重定向页面。发现后停掉任务、确认该目录只有这些垃圾、已删除；
  回头扫描此前下载的四个目录（论文 30、映射 24、文档 8、Lean 555 个文件），错误页 0 个。
  下载脚本已加 `curl -f`（HTTP 错误即失败）。
- 另有一次路径多拼一层 `OAI/`，被新加的 `-f` 如实报成 11 个失败，修正后重取。
- 缓存位置（`/tmp` 易失）：`/tmp/oai-math-audit/{paper,cc,lean-docs,me,me2,sb,ts2,ext}`；
  脚本在 `/tmp/rh-audit/oai-fetch/`（`fetch.sh`、`inventory.py`、`challenge_defs.py`）。
