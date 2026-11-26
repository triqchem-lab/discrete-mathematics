# OpenAI ω ≤ 9/4 形式化 · 只读审计注记（2026-11-25）

> **最新状态见文末《读完记录（2026-11-26）》。第一至六节是 11-25 的原始记录, 其中带作废标记的部分不要引用。**

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
> 【已被文末《读完记录》取代】仍未做: 四个子树依赖闭包的完整 sorry/axiom 扫描; 桥接引理与库内定义的忠实性审计
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


---

## 读完记录（2026-11-26, 按用户指示「先读完再决定」）

### A. 覆盖面——做到了什么、没做到什么

| 对象 | 规模 | 做到的 |
|---|---|---|
| 挑战件 `ComparatorChallenges/MatrixExponent.lean` | 136 行 | 全文逐行 |
| `SpectralBooks` | 840 件 / 84,747 行 | 全量文本扫描; 逐行读 `ExactExponent`、`SquareRankModel`、`DualExponent`; 陈述级读 `ArithmeticExponent`、`SquareExponent`、`Elongated`、`RectangularCircuitModel`、`Rank` 等; 模块说明读了几乎全部顶层文件与各子目录样例（838/840 件有模块说明） |
| `MatrixExponent` | 555 件 / 262,456 行 | 全量文本扫描; **逐行读主链 14 个文件**（见 B）; 定义级读 `SharedPrice`、`ArityReduction`、`Propagation`、`Rigidity`、`benchmark`/`U`、`Installable`、`Net`; 读 `contact_of_not_shared`、`shared_of_saving`、`propagation_of_*` 的陈述与骨架; 模块说明读了顶层与 8 个子目录（Valued/Prices/Routing/Shaving/Tagged/BatchDescent/Rounds） |
| `MatrixFields` | 354 件 / 181,751 行 | 全量文本扫描; 逐行读 `Main`、`Conclusions/AllFieldsBound`; **无模块说明**（18 万行里 1 条 docstring）, 文件名形如 `CapA1_1_14I0`; 其余未读 |
| 外部依赖闭包 | 直接依赖 47 个; 传递闭包开放规模 | 取回 1,013 件 / 142,957 行并扫描; 读 39/47 个直接依赖的模块说明; **队列里还有 870+ 个未取** |
| 合计 | **3,271 件 / 约 755,000 行** | 文本扫描 |

**没有做**: 读证明本身（绝大多数行）; 运行构建或 Comparator（按指示默认通过）; 读 `MatrixExponent` 里 Sphere（74 件）、Assembly（69）、Rectangle 内部（53）、Integral（39）、Transcript（20）等子目录的模块说明; 读 `MatrixFields` 的内容; 取完外部闭包。

### B. 主定理的陈述链（每一环读了原文, 没有发现空转的定义）

逐行读过的 14 个文件: `RationalCircuits`、`FieldFormula`、`Obstruction`、`UpperBound`、`PrimeFields`、`RankCriterion`、`Realization`、`Rectangle`、`ListBounds`、`Network`、`Tagged/Hard`、`BatchDescent/Hard`、`Rounds/Installation`、`Iteration`（后者读了 `incompatible` 的证明）, 以及聚合文件 `MatrixExponent.lean`。

1. `SpectralBooks/ExactExponent.lean:11` `square_exponent (F) [Field F] : formalOmega F 1 1 1 = 9/4 := (formalOmega_square_eq_omega F).trans (MatrixExponent.omega_eq F)`。
2. 挑战件自带的模型（`MatrixExponent.lean:13-102`）: 无除法直线程序, 加/减/乘各计 1; `FormalCorrect` 是 `MvPolynomial` 上的恒等式（有限域上也成立）。
3. `SquareRankModel.lean:43` `formalOmega F 1 1 1 = MatrixExponent.omega F`; 其中 `square_rank_iff` 把库内 `RankLE F n r` 等同于真实矩阵乘法张量 `matrixTensor F n n n` 的秩 ≤ r。
4. `MatrixExponent/RationalCircuits.lean`: `omega F := sInf {s | Admissible F s}`, 模型是**允许除法**的有理电路; `RankLE F n r := ∃ a b c : Fin r → Pos n → F, ∀ x y z, ∑ i, a i x * b i y * c i z = if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0`——标准张量秩分解。
5. `FieldFormula.lean:8` `omega_eq_and_rigidity (F) : omega F = 9/4 ∧ Rectangle.Rigidity F := contact_of_installations (fun p _ => Rounds.installable (ZMod p)) F`。
6. `Realization.lean` / `Obstruction.lean`: 有限域上的二选一——无共享价格则 `contact_of_not_shared`; 有共享价格则 `Rounds.installable` 给出压缩, 与 `ManyList (Realizes F)` 矛盾。
7. `Rectangle.of_prime_fields` + `PrimeFields.lean` 的 `prime_specialization`: 素域 ⟹ 所有域。
8. `UpperBound.lean:44` `upper_bound (F) : omega F ≤ 9/4`（经 `Rectangle.discrete_bound`、`closed_fulfills`, 输入是 `coeff_*` 证书）。
9. `MatrixFields/Conclusions/AllFieldsBound.lean`: `omega_lt_source_constant (F) : Arithmetic.omega F < 2.371054886006746`（每域无条件上界, 另一篇论文）。

### C. 下界的证明结构（据陈述与作者模块说明）

- 上界对所有形状成立: `Rectangle.upper : exponent F a b c ≤ U a b c`; `flat` 给出 c ≤ ab/(a+b) 时指数 = a+b（平凡紧）。
- 硬度: `Tagged.Hard F`: 存在 σ > 0, 对足够大的 w, 任何计算「带标签置换验证」核的 `Net`（**三价位网络**: 顶点是至多 3 个比特索引的 F 值表, `comp` 对中间线求和, `trace` 缩并）顶点数 ≥ 2^w·w·w^σ。这是受限模型里的无条件超线性下界, 不是一般电路下界。
- `ListBounds.lean`（只依赖 Mathlib）: `Seed`、`ManyList`、`Compression` 三个纯自然数谓词; `Iteration.lean:76` `incompatible : Seed P → ManyList P → Compression P → False`（证明逐行读过: 取 η = σ/4, b = min γ (σ/2)/2, J·b > 3, 迭代压缩 J 次）。
- 有限域 F: `omega F < 9/4 ⟹ SharedPrice (AlgebraicClosure F)`（`shared_of_saving`, 平凡地由 `contact_of_not_shared` 得到）⟹ `Compression (Realizes F)` ⟹ 矛盾。真正的内容在 `Valued/Shared.lean` 的 `contact_of_not_shared`（「同步或接触」）。
- 几何输入: `Propagation (Prices K)`（`Rectangle/Face/Contact.lean` 的 `propagation_of_tripod` / `propagation_of_potential`）; `Rigidity F` 是二选一（处处等于 U, 或在所有活跃形状严格小于 U）。

### D. 这个定理依赖仓库里的其他结果

四个子树 import 了 47 个子树之外的库内模块, 主要是 `Geometry.HyperbolicGroups`（组合式 CAT(0): 圆盘移动、切锥、Euler 势）、`Computability.BorderVNP`、`Computability.VPVNP`、`Hierarchy.PrimeFlats`（模块说明标题: 「Arithmetic class separations and square matrix multiplication over every field」）、`LinearAlgebra.TensorSpectrum`, 以及共享工具（`QuantumFactoring` 的布尔网络、`Perceptron.Sphere.GaussianPolar`、`SpanningForest.CauchyBinet`、`AffineBernstein.SphereIsometry`）。它的可信度与整个仓库绑在一起。

### E. 文本扫描（3,271 件）

`sorry` / `admit` 作策略 / `sorryAx` / `skipKernelTC` / `native_decide` / `axiom` 声明 / `opaque` 声明 / `implemented_by` / `unsafe` / `@[extern]`: **全部 0**。
非零且逐条看过的: `admit` 字样（散文, 外加 `BorderVNP` 里一个名为 `admit` 的 `local notation`）; `opaque` 字样 2 处（在文档注释内）; `partial def` 2 处（`BorderVNP/DiagonalOriginalStoredReportShape.lean`, 类型为 `MetaM Expr` 的元编程辅助）。非 OAI、非 Mathlib 的 import 只有 `Lean.Elab.Tactic.Omega`。

### F. 结论（限陈述层）

陈述链从 `square_exponent` 到 `Net` 的每一环都是具体、标准的定义, 没有发现定义漂移或空真; 证明结构可理解。**我没有读证明本身, 也没有运行构建**——所以这是「陈述层与结构层读完、未发现可疑之处」, 不是「我验证了这个证明」。若构建与 Comparator 通过（按指示默认如此）, 则结论是: 每个域上 ω = 9/4, α = 1/2, 矩形指数等于闭式; ω = 2 猜想为假。

### G. 对本仓库路径的意义

- `square_iff_prime_ranks`: 每域 ω = 9/4 等价于「每个素域上 rank(⟨n,n,n⟩) ≥ n^(9/4)」这族有限命题; GF(3) = ZMod 3 是其中一个素域。有限实例只能**反驳**、不能**确立**这个下界。→ 2026-11-26: 这族命题的陈述层已可在本库写出, 见 §J。
- `Tagged.Hard (ZMod 3)` 与 `ManyList (Realizes (ZMod 3))` 是关于 GF(3) 的定理——离散寄存器在这个问题上的准确位置是「有限素域上的秩与网络实例」, 不是渐近指数本身。
- 下界里唯一与域无关、不需要枚举的一环是 `ListBounds.incompatible`（对一切 w 成立的软论证）。若要在本库做一件事, 镜像它是最有界的; 但它用到实指数与「最终」量词, 需要先设计一个不用实数的表述（宪法禁无理数）。~~**未开始。**~~ → 2026-11-26 已做完, 见 §H。

### H. 软核的 ℕ 镜像——已形式化（2026-11-26, 回执 `6982c9a1`）

§G 第三条说的「镜像 `ListBounds.incompatible`」已做完: `src/Sovereign/Algebra/LinearAlgebra/ListBounds.agda`
（1222 行, exit=0, 0 postulate, 0 REWRITE 规则, 只依赖标准库）。

| Lean（原文行号, 2026-11-26 读到） | Agda（ℕ） |
|---|---|
| `listBits w = 2 * w * 2 ^ w`（:14） | `lb-listBits` |
| `Seed P`（:16） | `lb-Seed P lb-listBits` |
| `ManyList P`（:20） | `lb-Many P lb-listBits` |
| `Compression P`（:25） | `lb-Comp P lb-listBits (λ w → w * w)` |
| `incompatible : Seed P → ManyList P → Compression P → False`（`Iteration.lean:76–77`） | ★ `lb-incompatible-lists` |

**怎么不用实数**（[设计说明]）:
- 分数次幂只出现在不等式里 → 两边乘方成整数不等式: σ = p/q 时 `t·n·w^σ < 3m` 写成 `(t·n)^q · w^p < (3m)^q`;
  `d ≤ n^(1/D)` 写成 `d^D ≤ n`; `m ≤ n^(21/20)` 写成 `m^20 ≤ n^21`。
- 压缩里 h 的分数次幂写成「对一切满足 `u^G ≤ h^g`、`h^e ≤ v^E` 的自然数 u、v」。
- 证明把 w 取在子序列 w = W^N0 上（N0 = 16·q·G）, w 的幂全是 W 的整数次幂; n、h 抽象成满足增长条件的函数。
- Lean 原文的量词结构逐条对上了: 压缩是 ∀η>0 ∃γ>0 ∀δ>0（γ 不依赖 δ）[对照原文读出]; 压缩**不带** `t ≤ listBits` 前提。

**边界（必带）**:
1. 「Lean 的实数陈述 ⟹ 本 ℕ 陈述」这座桥**未形式化** [手工论证·未验证]。桥的左端要实指数幂（要 ℝ）,
   本库宪法禁无理数, 写不出; 只能在 Lean 一侧补一条引理（本仓库不做）。
   所以它是软核在 ℕ 上的一条**独立**定理, 不是 Lean 那条定理的形式化推论。
2. 证明是独立重构（写成时只读过 Lean 证明的开头）; 事后通读 `Iteration.lean`（164 行）确认两边**同构**:
   `lb-step-Y` ↔ `absorb`、`lb-Inv` ↔ `iterate`、副本界 δ = 1/(40·J) ↔ `copies`、终局矛盾 ↔ 末段, 都在 η = σ/4 处调用压缩。
   两处差别: 衰减率（Lean `b = min γ (σ/2)/2`, 本文件 min(γ/4, σ/16) 更保守）; 取 w（Lean 用 Mathlib 渐近工具, 本文件 w = W^N0）。
3. 只镜像软核。硬度与压缩本身不在这里; 这不是任何域上任何矩阵乘法下界的证明; 不改变 ω = 9/4 的审计状态。

**旁证（是证据不是证明）**: `engineering/oracle_list_bounds.py` 10 项 ALL_PASS（整数/分数精确, 禁浮点）——
含桥接的随机抽样 G1–G3 与 h 桥 H（`w ≤ clog 2 (listBits w) ≤ w²` 自 w = 2 起, 核到 3000）;
`engineering/tests/test_oracle_list_bounds.py` 11 个 unittest。
⚠ 本件顺序与「先算后验」相反: Agda 先行, oracle 事后核对（首版迭代一步那项空转, 靠打印触发数发现并修正）。
**非空真（同文件 §11）**: 主定理是「四条假设 ⟹ ⊥」, 可能靠某条假设不可能成立而空真。§11 给出四个内核检查过的见证 P,
说明去掉任意一条假设后其余三条同时成立（`lb-consistent-SMG`/`SCG`/`MCG`/`SMC`）,
配合主定理得 `lb-necessary-C`/`M`/`S`/`G`——四条缺一不可。

已登记: `PROVEN.md` §十五 M15。

### I. 证明阅读（2026-11-26）

用户指示「读证明」。论文正文 24 个证明性 tex（7,214 行）逐行读完；Lean 主干逐环读到底。
完整台账见 [`OpenAI-omega-9-4-证明阅读-2026-11-26.md`](OpenAI-omega-9-4-证明阅读-2026-11-26.md)。
要点: 论文 ↔ Lean 对照表（每行标注核对深度）；挑战件 15 个定义与库内原件逐字相同（15/15）；
Lean 陈述强于论文；Lean 的硬度走对角化、与论文的两情形路线不同；CAT(0) 比较不等式在 Lean 里是定理；
`MatrixExponent/` 555 件 263,011 行逃生口扫描为 0。**没有运行构建，没有运行 Comparator。**

### J. GF(3) 的陈述层与离散组合层——已形式化（2026-11-26, A/B 回执 `f18cdc4f`, C 回执 `cf06d543`, D 与本节同批提交）

§G 第一条说的那族有限命题, 此前在本库**连陈述都写不出**（没有秩分解谓词）。M16 把陈述层与离散组合层镜像过来,
全部在 `src/Sovereign/Algebra/LinearAlgebra/`, 四件都 exit=0、0 postulate、0 REWRITE 规则:

| Lean | Agda（GF(3)） | 说明 |
|---|---|---|
| `RationalCircuits.lean:48 RankLE` | `record RankLE₃`（`TensorRankGF3.agda:87`） | 结构常数形式: Σ_k a k x ⊗ b k y ⊗ c k z ≡ T(x,y,z) |
| （M13 的接桥） | ★ `strassen-is-rank-form` / ★ `rank-strassen : RankLE₃ 2 7` | Strassen 七乘方案就是一个 7 项秩分解 |
| `Flattening.lean:6 rank_lower : n ^ 2 ≤ r` | ★ `rank-lower`（`TensorRankFlattenGF3.agda:272`） | Lean 走展平后矩阵的秩; 本库走计数（标准基落在张成里 ⟹ 单射 `Fin (3^(n²)) → Fin (3^r)`） |
| `RankPower.lean:12 rank_mul` / `:15 rank_pow` | ★ `rank-mul` / ★ `rank-pow`（`TensorRankPowGF3.agda:290` / `:310`） | 张量积与取幂; ★ `rank-strassen-pow : ∀ k → RankLE₃ (2 ^ k) (7 ^ k)` |
| `key/MatrixExponent.lean:45 square_iff_prime_ranks`（p = 3） | `ω₃-boundary`（`TensorRankGF3.agda:298`, **无居民**） | 外部下半的陈述; 本库不证、未推进 |
| `FieldExtension.lean:72 exponent_lt_iff_rank`（取形状 (1,1,1): `Rectangle/Bounds.lean:15 square`） | `Saving₃` / `ω₃-upper`（`TensorRankUpperGF3.agda:94` / `:98`, 上半**无居民**） | 上半的有限形态: ∀ p q, 9q < 4p → ∃ n r, 2 ≤ n ∧ RankLE₃ n r ∧ r^q < n^p |
| （Strassen 的覆盖范围） | ★ `strassen-saving`（`:110`）: `∀ p q → 0 < q → 17 * q ≤ 6 * p → Saving₃ p q` | n = 2^(6q)、r = 7^(6q); 离 9/4 还有空档 |
| （两半的关系） | ★ `saving-above` / ★ `exactness₃`（`:166` / `:194`） | 有下半时任何节省满足 9q < 4p; 两半一旦成立, 节省恰好是比值在 9/4 之上的 (p, q) |
| （尺寸 3 的见证; Lean 侧无对应——Lean 的 9/4 见证非显式, `Coefficients.lean:43 candidate := Classical.epsilon …`） | ★ `rank-laderman : RankLE₃ 3 23` / `rank-eqL`（`TensorRankLadermanGF3.agda:781` / `:691`, 729 条 refl, M17 回执见 §J 末） | Laderman 1976 的 23 门（证书: GitHub `RakTikoo/matmul-333-tensor-rank`, 系数 ∈ {-1,0,1}, ℤ 恒等式 ⟹ GF(3)）; 配 ★ `laderman-saving`（p/q ≥ 20/7）与 ★ `laderman-not-below`（(3,23) 从不越过 17/6） |

**路径上还差什么**（三层; 第 1 层与第 3 层的前半是已核对的, 其余是 [阅读判断]）:
1. 陈述层——已齐: 谓词、接桥、下界方向（展平）、上界方向（张量幂见证）、两半的有限陈述（`ω₃-boundary` / `ω₃-upper`）。
2. 见证层——每个尺寸 2^k 有内核检查过的见证（项数 7^k）。n = 2 处库内 4 ≤ r ≤ 7, 外部定理给 r ≥ 5, 「秩恰为 7」[直觉·未验证]。
   → **2026-11-26 更新（M17, 用户定案「选项 1 小规模版」）**: 尺寸 3 的 GF(3) 分解已到手——★ `rank-laderman : RankLE₃ 3 23`
   （Laderman 23 门; n=3 处库内两方向 9 ≤ r ≤ 23）。但它**不进空档**: 比值 20/7 ≈ 2.857 差于 17/6 ≈ 2.833
   （★ `laderman-not-below` 内核核验 (3,23) 从不越过 17/6）。空档的精确化（oracle 判据 7, 纯整数核对）:
   n=3 上 r=21 即可进（21^5 < 3^14, 84 < 85）、r=22 也可（首个 (31,11) ≈ 2.818）、r=23 不行;
   有界爬山（6×12000 步, 最优失配 215/729）只是有界尝试, 「rank ≤ 22」存在性是公开问题 [阅读层·未验证]。
   **仍未做**: 双线性归约（Lean `Bilinearize.lean:111`: q 个非标量门 ⟹ 秩 ≤ 2q）——要先定义电路模型 [未验证·路线推测]。
3. 证明层——**陈述层已核对**（本轮读了 `UpperBound.lean` 全文、`Coefficients.lean` 全文、`Rectangle.lean` 全文、`FieldExtension.lean:17–97`）:
   上界也有有限的秩分解形态（`exponent_lt_iff_rank`）; 但 Lean 那边靠 9/4 的见证不是显式的——
   `Coefficients.lean:43 candidate := Classical.epsilon (fun k => ¬ Fulfills k.carrier)`: 上界机器在一个用选择公理挑出的代数闭域上工作
   （同文件头注: The tensor argument only uses the field axioms and algebraic closure）, 再由 `closed_laws`（`:48`）反证式地推广到一切代数闭域;
   实数只出现在 `(A : ℝ) * B ≥ 0` 这类位置（`UpperBound.lean:31–38`）。
   所以缺的东西可以说准了: **不是陈述, 是 9/4 与 17/6 之间的见证**（GF(3) 上 r < n^(p/q) 的分解, 9/4 < p/q < 17/6）,
   外加把 Lean 的实数陈述接到分数形态的那座桥 [手工论证·未验证]。
   `Upper/`（32 件 5106 行）与 `Integral/Upper/`（33 件 4828 行）的证明本身没有读。

**本批更正**: `TensorRankGF3` 头注与 oracle 文档曾写「oracle 逐字发射 / 贴用 64 条子句」——实际组织是 `mm-basis` 16 条 × 4 个输出位置, 已按代码改正。

已登记: `PROVEN.md` §十五 M16、§十六 M17（三条机器轨互证: oracle ALL_PASS / Agda 内核 exit=0 / TriRV 三进制 VM 正件 exit=0 负控 exit=66 与预言一致）。

### K. 上界机器的构造链——已通读到「分解生产点」, 非构造性定位（2026-11-26, M17 之后「选项 3 入口」）

问题: Lean 的 9/4 构造能否在 GF(3) 上变成显式分解表? 动作: 把从「域」到「秩分解」的**每一条链环**通读一遍
（区别于 §F 的陈述层通读——这次读的是证明体）。以下每一环都有 file:line 核对动作:

```
域 F ──small_field(UpperBound.lean:9-20)──▶ K = ZMod p 或 ℚ
    ──exponent_extension(FieldExtension.lean:89, 标量扩张不改指数)──▶ 代数闭包 K̄
    ──closed_fulfills(UpperBound.lean:22-28): closed_laws 喂五个组件──▶ Fulfills K̄
    ──五定律(character_bound 等, 全部汇入 exponent_le_of_characters)──▶ 指数 ≤ s
                                     │
    反证: exponent > s ──price_gap(Rectangle/Support.lean:65, r = ⌈9·n^s⌉₊)──▶ n, r 有价差
    ──price_dots(CharacterRank.lean:84-104, side n a ≤ 2·n^a 的「取顶每配对至多两倍」)──▶
        一切单调 NNReal-特征 f: f(dots) < f(r)
    ──Spectrum.strictComparison(Spectrum/Comparison.lean:215)──▶ ∃ C: ∀ p, dots^p ≤ (C·r^p : TensorClass)
    ──rank_of_dots(CharacterRank.lean:60-76)──▶ RankLE Coeff (side^p) (r^p·C)
    ──exponent_lt_of_rank(FieldExtension.lean:37)──▶ 与 exponent > s 矛盾
```

**分解的唯一生产点** = `rank_of_dots` + `CoefficientTensor.rank_le_iff`（`Upper/Tensor/Rank.lean:150`:
`rank T = Nat.find (rankAtMost_finite T)` 的经典最小数）。这一环本身是有限可提取形态——**但半环比较从哪来**:
`strictComparison` 的证明 = 商掉「y ≤ x」的 RingCon（等式层, 域无关）+ **紧性/分离**
（`Spectrum/Comparison.lean:52-104` `closed_points`/`compact_points`/`separated`: **无穷积紧性**
`isCompact_pi_infinite` + 极小元存在 + 有限子覆盖）——常数 C 只以 `∃ C` 给出, 无算法。

**判定: 不能直接变成 GF(3) 上的显式分解表。** 非构造性有三层, 每层都是原则性的:
1. **紧性层**（原则性最强）: strictComparison 的 C 来自无穷积空间上的紧性论证（Tychonoff 级）, 没有 C 的任何界;
2. **ε-slack 层**: `price_gap` 的 n 来自实数发散论证, `absorb_overhead`（FieldExtension.lean:49）的 k 是 `tendsto` 的纯存在;
3. **基域层**: `Coeff = Classical.epsilon …`（Coefficients.lean:43）。GF(3) 只经 `exponent_extension` 绕道代数闭包被覆盖——**构造从不发生在 GF(3) 上**; 机器内部还要求无穷域（`exists_nonzero_nodes`, Coefficients.lean:56 需要 `Infinite F`）与多项式插值/分离一族（`Upper/SeparationInterpolation`、`Upper/PolynomialValues`）, 这些是有限域上的真障碍。

**对我们路径的可迁移件（读出的正面产出）**:
- 「半环比较 ⟹ RankLE」的框架与 `RankLE₃` 同构——我们的 M16/M17 走的是**反方向**（具体表 ⟹ RankLE₃ ⟹ Saving₃）, 恰好是 Lean 机器不可构造化那一环的显式替代;
- 五定律是有限可核对的组合命题（`character_bound`: 4(pX·BC + pY·AC + pZ·AB) ≤ (A+B+C)² 等）——它们的 GF(3) 版本可以逐条机器核对, 但即便全成立, 「定律 ⟹ 分解」的桥（紧性）在 GF(3) 上没有显式版本, **定律不产表**;
- 因此「把 Lean 构造改造成表」这条路线**封存**: 显式化的空间在（a）小尺寸见证搜索（M17 已做 3×3; r ≤ 21 是公开问题级）、（b）五定律的 GF(3) 有限化核对（可做, 产数据点不产表）。

**阅读覆盖（本轮）**: `UpperBound.lean` 全文 44 行、`Coefficients.lean` 全文 69 行、`Rectangle/CharacterRank.lean` 全文 115 行、`Rectangle/Poly.lean` 全文 124 行、`Spectrum/Comparison.lean` 全文 260 行、`FieldExtension.lean:37-60`（`exponent_lt_of_rank`/`absorb_overhead` 证明体）、`Rectangle/Support.lean:65-80`（`price_gap` 证明体）、`Upper/Tensor/Rank.lean` 关键定义（`rank`/`rank_le_iff`/`TensorClass` 商结构）。**未读**: `Sparse/Degree.lean`、`Folding/Swap.lean`、`Profile/Pairing.lean` 的定价细节与 `Upper/Character/*` 内部——全部在 `exponent_le_of_characters` 上游（定价层, 非构造层）, 不改变本判定 [边界标注]。
