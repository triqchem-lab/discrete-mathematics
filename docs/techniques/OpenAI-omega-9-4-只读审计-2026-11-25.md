# OpenAI ω ≤ 9/4 形式化 · 只读审计注记（2026-11-25）

> ## ⚠ 勘误与撤回（2026-11-26）—— 第三节与 F3/F4 作废
>
> 我在 11-25 据本注记向用户报告: 「Lean 只承载 ω(ℂ) ≤ 9/4 上界」「下界连形式化都没有」
> 「对照件三条 sorried 是未交付欠账」「F4 结案: 内部库无 ω ≥ 9/4」「Θ(n^2.25) 口径超出 Lean 承载」。
> **这些结论全部错误, 公开撤回。**
>
> 错在哪:
> 1. 只审了相关子树中的一个。矩阵乘法指数相关的 Lean 至少分布在四个子树:
>    `LinearAlgebra/MatrixMultiplication`(509) / `SpectralBooks`(840) / `MatrixExponent`(555) /
>    `MatrixFields`(354)。我只取了第一个, 却把「509/509 全量 rg 零命中」说成全库结论。
> 2. 解模块的位置一直写在挑战件旁边: `ComparatorChallenges/MatrixExponent.json` 的
>    `solution_module` = `OAI.LinearAlgebra.SpectralBooks.ExactExponent`; 挑战文件的命名空间
>    也是 `LinearAlgebra.SpectralBooks`（F2 记下了这个命名, 却没去查）。
> 3. 内容搜索的输出被 `head -12` 截断过; 按名字搜索也盖不住别的命名。
> 4. 「对照件带 sorry = 欠账」是误读。全库 852 个结果都以「挑战件（陈述 + sorry）+ 解模块 +
>    Comparator 工具核对」的形式给出（`ComparatorChallenges/README.md`:
>    `lake env comparator <x>.json`; JSON 含 `permitted_axioms` 白名单）。带 sorry 的挑战件是机制本身。
>
> 更正后的一手事实（2026-11-26, 代理取回）:
> - `SpectralBooks/ExactExponent.lean:11`
>  `theorem square_exponent (F : Type*) [Field F] : formalOmega F 1 1 1 = (9 : ℝ) / 4 :=
>     (formalOmega_square_eq_omega F).trans (MatrixExponent.omega_eq F)`
>  同文件 `dual_exponent : formalAlpha F = 1/2`、`rectangular_exponent`。该文件 sorry / axiom / native_decide 均为 0。
> - 核心等式 `MatrixExponent.omega_eq F` 在 `OAI.LinearAlgebra.MatrixExponent.*`（555 件）——**未读**。
> - **`SpectralBooks` 840/840 全量**、**`MatrixMultiplication` 509/509 全量**两个子树, 文本扫描全部 0 命中:
>  `sorry` / `admit`（作策略; 6 处命中均为文档注释里的英文动词）/ `sorryAx` / `skipKernelTC` / `native_decide` /
>  `axiom` 声明 / `opaque` / `implemented_by` / `unsafe` / `partial def` / `@[extern]`。这是文本扫描, 不等于构建。
> - 桥接引理（`SpectralBooks/SquareRankModel.lean:43`, 只读陈述）:
>  `theorem formalOmega_square_eq_omega (F : Type*) [Field F] : formalOmega F 1 1 1 = MatrixExponent.omega F`。
>  库里同时存在三个指数定义: 挑战件自带的 `formalOmega`（用挑战件内自定义的 `MatrixAlgorithm`/`FormalCorrect`/`wireDimension`）、
>  `SpectralBooks/ArithmeticExponent.lean:29` 的同名 `formalOmega`、`MatrixMultiplication/Model.lean:95` 的
>  `omega F := sInf {τ | AdmissibleExponent F τ}`; `MatrixExponent.omega F` 的定义在未读的子树里。
>  这几个定义是否指同一个对象, 是忠实性审计的核心, 未完成。
> - `MatrixFields.json` → 解 `OAI.LinearAlgebra.MatrixFields.Main`, 定理
>  `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`（每域上界; 未读）。
>
> 仍未做: 四个子树依赖闭包的完整 sorry/axiom 扫描; 桥接引理与库内定义的忠实性审计
> （`formalOmega_square_eq_omega` 把挑战件的 `formalOmega` 接到库内 `omega`, 是否同一对象）;
> Comparator 是否通过（按指示不运行）。
> 正确表述: **OpenAI 仓库对「每个域上 ω = 9/4、α = 1/2、矩形闭公式」给出了完整陈述与解模块映射;
> 我此前的一切负面判断撤回; 忠实性审计未完成。**
>
> 接口定理（`lean/OAI/LinearAlgebra/MatrixExponent.lean` 聚合文件; **只读了陈述, 证明与被引用的定义未读**）:
> - `square_iff_prime_ranks : (∀ F [Field F], omega F = 9/4) ↔ ∀ (p : ℕ) [Fact p.Prime] (n r : ℕ), 2 ≤ n → RankLE (ZMod p) n r → n ^ 9 ≤ r ^ 4`
> - `square_of_prime_ranks (h : 同上) (F) : omega F = 9/4`
> - `square_of_network_bounds`（ManyList 硬度 + Compression）、`square_of_tag_and_arity`（Tagged.Hard + Lookup.ShortTag/ArityReduction）—— 同为「素域上的假设 ⇒ 每域 ω = 9/4」。
>
> 这对本仓库路径的意义: 「每域 ω = 9/4」等价于一族**有限**命题——每个素域 ZMod p 上 n×n 矩阵乘法的秩 ≥ n^(9/4)。
> GF(3) = ZMod 3 就是 p = 3 的情形, 这是离散寄存器与该问题准确的接点。实例: n=2 要求 r ≥ 5（已知恰 7）; n=3 要求 r ≥ 12;
> n=12 要求 r ≥ 269（Hopcroft–Kerr 的 2n²−1 = 287 已更强）。n^(9/4) 要到 n 很大时才超过经典的 ~2–3n² 界,
> 所以有限实例只能**反驳**、不能**确立**这个下界。
>
> 另: 第四节「Alpöge 的 anyGeometry 隐性空真」的措辞违反 `Sovereign-RH-Constructive-Path.md`
> 零节红线, 撤回该措辞。

> 性质：**anyGeometry 式一手审计**（只读、零构建、按用户指示默认编译通过）。
> 对象：`github.com/openai/math`（Lean, v4.34.1, main@adc7f12 附近, 2026-11-25 仍活跃推送）。
> 审计面：矩阵乘法指数 ω ≤ 9/4 = 2.25 的形式化陈述与宣传口径的忠实性。
> 覆盖率声明：blobless 元数据全量（200,961 文件清单）+ 内容抽样 **69/509**（被审子树
> `OAI/LinearAlgebra/MatrixMultiplication/` 的 13.6%——GitHub 连接中断, 余件待取）。
> 每条一手事实附文件行号; 推测一律标注。

## 一、代码量回答（用户问: 证明需要这么多代码吗）

| 层 | 规模 | 本地可编译性 |
|---|---|---|
| 全库（OpenAI 数学计划合集: Analysis 29,367 / NumberTheory 29,314 / AlgebraicGeometry 24,364 / Combinatorics 16,645 …） | 200,961 文件 / **189,309 个 .lean** | ❌ Alpöge 级, 全库编译不可行 |
| **ω=9/4 结果本体**【作废: 这只是四个相关子树之一, 见顶部勘误】 `OAI/LinearAlgebra/MatrixMultiplication/` | **509 个 .lean**（Arithmetic 12 / AuxiliarySeparation ~80 / CoppersmithWinograd 29 / Duality ~30 / FieldConstruction ~65 / JointExtraction ~60 / Tensor ~33 / Numerical 8 …） | ✅ 子树 + Mathlib 缓存可行 |

对照: Alpöge RH = 175,187 .lean（17.4M 行, 本机 210GB 构建未完成）——同级全库,
但 ω 结果子树占全库 0.27%。**本机磁盘占用 22MB**（blobless 元数据 7.3MB + 4 个抽样件）。

## 二、一手事实（F 系列, 附文件行号）

| # | 事实 | 位置 |
|---|---|---|
| F1 | 对照件 `ComparatorChallenges/MatrixExponent.lean` 全 136 行, 含 **3 处 `sorry`**: `square_exponent : formalOmega F 1 1 1 = 9/4`、`dual_exponent : formalAlpha F = 1/2`、`rectangular_exponent`（闭公式）——**sorried-by-design**: 对照件是「待外部核验的挑战书」, 非已证库 | `lean/ComparatorChallenges/MatrixExponent.lean:106-131` |
| F2 | 对照件命名空间 = `LinearAlgebra.SpectralBooks`（「谱册」——渐近谱方法的命名痕迹） | 同文件 end 行 |
| F3 【作废—见顶部勘误】 | 内部主定理 `Main.lean` **只承载上界**: `complex_omega_le_nine_quarters : Arithmetic.omega ℂ ≤ 9/4 := AuxiliarySeparation.omega_le_nine_quarters`——单行再导出, **ℂ only, ≤ only** | `…/MatrixMultiplication/Main.lean:12-14` |
| F4 【作废—见顶部勘误: 解在 SpectralBooks/ExactExponent.lean】 | **精确等式（含下界 ω ≥ 9/4）在内部库的交付位置未定位**（69/509 已扫, 零 sorry/axiom 命中; `nine_quarters` 命名全库 0 处; `LowerBound.lean` 只有 naive 模型代价下界与 `2 ≤ rectangularOmega` 平凡件） | 待取余 ~440 件后复查 |
| F5 | **模型层忠实性 ✓**: `MatrixAlgorithm F a b c` 的 Correct 定义 = 全多项恒等式 `∀ A B i k, eval … = ∑ j, A i j * B j k`（`Complexity.lean:40-43`）; 代价 = 门计数（divisions excluded ✓ docs/107 口径）; 指数 = `sInf {τ \| FormalAdmissibleExponent …}` 带 ε-slack（`MatrixExponent.lean:99-102`）——教科书定义形态, 无空真迹象 | 见左 |
| F6 | 方法 = **CW75 基张量 + 熵/Gibbs 势函数 + Farkas 凸对偶分离 + 卷积张量精确秩**（非激光法）: `CoppersmithWinograd/` 29 件 + `Entropy/`/`FieldConstruction/`（ActiveGibbs 等）+ `AuxiliarySeparation/Convex/Farkas.lean` + `Convolution/RankLowerBound.lean`（**卷积张量精确秩, 恒等子式 + 评估/插值**）——与 Ahle「potential function on tensors, contradiction from the simple convolution tensor」逐词对上 | 文件名清单 + 各文件头 |
| F7 | Farkas = **有限有理锥对偶分离**: 「负规范化向量无正整倍数 → 存在规范化非负线性泛函」——下界的正性来源 = 谱上的分离型正性（与预印本《Euclidean geometry in the asymptotic spectrum of tensors》同名异构） | `AuxiliarySeparation/Convex/Farkas.lean:15-24` |
| F8 | Numerical/ 8 件证书（AllFieldCertificates* / ComplexCertificates*）= 数值不等式的 Lean 内承证（docs/107: 「No numerical inequalities remain as hypotheses」）——**与本仓库 oracle 先算后验同构** | `Numerical/` 文件清单 |
| F9 | 四篇预印本（2026-09/11）: Below 2.258 / Staggered extraction / **The matrix multiplication exponent is nine fourths** (11-24) / Euclidean geometry in the asymptotic spectrum (11-24) | `lean/docs/107.md` |

## 三、口径差【整节作废—见顶部勘误】

| 口径 | 来源 | 形式化承载状态 |
|---|---|---|
| **上界 ω(ℂ) ≤ 9/4** | 主张的保守读法 | ✅ Main.lean 单行再导出 `AuxiliarySeparation.omega_le_nine_quarters`（内部链 69 件抽样零 sorry） |
| **等式 ω(F;1,1,1) = 9/4（每域, 含下界）+ α(F)=1/2 + 矩形闭公式** | 对照件 F1（sorried） | ⏳ 内部交付位置未定位（F4）——**若内部库无 ω ≥ 9/4, 则「精确指数/Θ(n^2.25)/驳 ω=2」的宣传口径未被形式化承载** |
| 「Lean verification passes」 | 内部审查 | ✅ 但对照件含 3 sorry（lakefile 将对照件入构建）——「通过」指内部库可编译 + 对照挑战由比较器另行核验, **非零 sorry 口径**（与 Alpöge 仓库 0-sorry 形态不同, 不可混比） |

**【作废—见顶部勘误】[F4 已结案 2026-11-25 续, 代理恢复后 509/509 全量出料]**: 内部库**不含 ω ≥ 9/4 下界定理**——
全子树 rg: `nine_quarters`/`ge` 方向零命中（仅 `≤` 链）; `AuxiliarySeparation/Main.lean` 头注自述
「Theorem 1.1 … **complex** square matrix multiplication … consequently an **upper bound** of 9/4」
（复杂域 + 上界, 显式自限）; Obstruction.lean 头注亦显式免责「do not assert the existence of a
tensor spectrum or the separation argument」。全库亦无 `2.3710548`（docs/107 所称每域
ω(F) < 2.371054886006746 的 Lean 交付不在本子树）。**对照件的三条 sorried 挑战（每域等式 9/4 /
α=1/2 / 矩形闭公式）= 内部库未交付的欠账**——宣传口径（Θ(n^2.25)/驳倒 ω=2）超出 Lean 承载。
另: 交付链骨架与本仓库 NormFormPositive 同构（展开引理 → 段名化 → prem 乘入 → sInf 收口）,
两库独立收敛（同构发现 #2）。

## 四、W-筛网四网应用（对 ω=9/4 结果本身）

| 网 | 判读 |
|---|---|
| W1 证书可枚举 | ✅ Numerical/ 8 件 = 数值证书的 Lean 内封存（先算后验同构）; Farkas 的有理证书提取 = 分离的枚举承证 |
| W2 共轭可承证 | ✅ `AuxiliarySeparation/Character/Symmetrization.lean` 等字符/对称件——张量层次的对称承证 |
| W3 正性可定位 | ✅ **F7: Farkas 锥对偶 + 渐近谱**——下界的正性来源显式定位在锥分离（与本仓库 W3 的 Schwarz 骨架同构: 谱上的正性 → 指数界） |
| W4 非循环 | ⏳ 对照件 sorried-by-design 是**显式的未证挑战**（诚实形态, 与 Alpöge 的 anyGeometry 隐性空真**相反**【措辞撤回: 违反 Constructive-Path 零节红线】）——非循环性取决于内部链是否蕴含对照件, 待蕴含校验器核查 |

## 五、与本仓库的同构对照（用户框架回接）

1. **下界正性来源 = 渐近谱上的分离** ↔ 用户「本征值-模/本体-投影」框架: 谱点即投影, 分离泛函即本体侧的
   非负坐标——「为什么会偏离」在 ω 语境 = combination loss（组合损耗）——五路线诊断里 Connes 路线的
   「谱缺失」反义（此处谱是**造出来的**——Farkas 保证存在）。
2. **Numerical/ 证书件 ↔ oracle 先算后验**: 两库独立收敛到同一纪律（数值断言必须在形式化内封存）。
3. **对照件 sorried-by-design ↔ 对照挑战范式**: 与本仓库 ComparatorChallenges 思路同构
   （挑战书显式 sorry, 已证库另行蕴含）——「Lean 通过」的口径必须逐库问清（Alpöge 0-sorry vs 此处 3-sorry）。

## 六、待办

1. 网络恢复: 稀疏取余 ~440 件 → rg 查 ω ≥ 9/4 下界的内部交付（`AuxiliarySeparation/Spectrum/Obstruction.lean`、`Duality/ExponentBound.lean` 优先）→ F4 升级或结案。
2. 蕴含校验器形态确认: 「Comparator checks」的工具是哪个、对照件与内部定理的蕴含如何机检。
3. (可选) 509 文件 + Mathlib 缓存本地编译复核（用户已豁免, 记为可选）。
