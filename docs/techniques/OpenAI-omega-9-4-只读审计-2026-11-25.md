# OpenAI ω ≤ 9/4 形式化 · 只读审计注记（2026-11-25）

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
| **ω=9/4 结果本体** `OAI/LinearAlgebra/MatrixMultiplication/` | **509 个 .lean**（Arithmetic 12 / AuxiliarySeparation ~80 / CoppersmithWinograd 29 / Duality ~30 / FieldConstruction ~65 / JointExtraction ~60 / Tensor ~33 / Numerical 8 …） | ✅ 子树 + Mathlib 缓存可行 |

对照: Alpöge RH = 175,187 .lean（17.4M 行, 本机 210GB 构建未完成）——同级全库,
但 ω 结果子树占全库 0.27%。**本机磁盘占用 22MB**（blobless 元数据 7.3MB + 4 个抽样件）。

## 二、一手事实（F 系列, 附文件行号）

| # | 事实 | 位置 |
|---|---|---|
| F1 | 对照件 `ComparatorChallenges/MatrixExponent.lean` 全 136 行, 含 **3 处 `sorry`**: `square_exponent : formalOmega F 1 1 1 = 9/4`、`dual_exponent : formalAlpha F = 1/2`、`rectangular_exponent`（闭公式）——**sorried-by-design**: 对照件是「待外部核验的挑战书」, 非已证库 | `lean/ComparatorChallenges/MatrixExponent.lean:106-131` |
| F2 | 对照件命名空间 = `LinearAlgebra.SpectralBooks`（「谱册」——渐近谱方法的命名痕迹） | 同文件 end 行 |
| F3 | 内部主定理 `Main.lean` **只承载上界**: `complex_omega_le_nine_quarters : Arithmetic.omega ℂ ≤ 9/4 := AuxiliarySeparation.omega_le_nine_quarters`——单行再导出, **ℂ only, ≤ only** | `…/MatrixMultiplication/Main.lean:12-14` |
| F4 | **精确等式（含下界 ω ≥ 9/4）在内部库的交付位置未定位**（69/509 已扫, 零 sorry/axiom 命中; `nine_quarters` 命名全库 0 处; `LowerBound.lean` 只有 naive 模型代价下界与 `2 ≤ rectangularOmega` 平凡件） | 待取余 ~440 件后复查 |
| F5 | **模型层忠实性 ✓**: `MatrixAlgorithm F a b c` 的 Correct 定义 = 全多项恒等式 `∀ A B i k, eval … = ∑ j, A i j * B j k`（`Complexity.lean:40-43`）; 代价 = 门计数（divisions excluded ✓ docs/107 口径）; 指数 = `sInf {τ \| FormalAdmissibleExponent …}` 带 ε-slack（`MatrixExponent.lean:99-102`）——教科书定义形态, 无空真迹象 | 见左 |
| F6 | 方法 = **CW75 基张量 + 熵/Gibbs 势函数 + Farkas 凸对偶分离 + 卷积张量精确秩**（非激光法）: `CoppersmithWinograd/` 29 件 + `Entropy/`/`FieldConstruction/`（ActiveGibbs 等）+ `AuxiliarySeparation/Convex/Farkas.lean` + `Convolution/RankLowerBound.lean`（**卷积张量精确秩, 恒等子式 + 评估/插值**）——与 Ahle「potential function on tensors, contradiction from the simple convolution tensor」逐词对上 | 文件名清单 + 各文件头 |
| F7 | Farkas = **有限有理锥对偶分离**: 「负规范化向量无正整倍数 → 存在规范化非负线性泛函」——下界的正性来源 = 谱上的分离型正性（与预印本《Euclidean geometry in the asymptotic spectrum of tensors》同名异构） | `AuxiliarySeparation/Convex/Farkas.lean:15-24` |
| F8 | Numerical/ 8 件证书（AllFieldCertificates* / ComplexCertificates*）= 数值不等式的 Lean 内承证（docs/107: 「No numerical inequalities remain as hypotheses」）——**与本仓库 oracle 先算后验同构** | `Numerical/` 文件清单 |
| F9 | 四篇预印本（2026-09/11）: Below 2.258 / Staggered extraction / **The matrix multiplication exponent is nine fourths** (11-24) / Euclidean geometry in the asymptotic spectrum (11-24) | `lean/docs/107.md` |

## 三、口径差（★ 本审计的核心发现）

| 口径 | 来源 | 形式化承载状态 |
|---|---|---|
| **上界 ω(ℂ) ≤ 9/4** | 主张的保守读法 | ✅ Main.lean 单行再导出 `AuxiliarySeparation.omega_le_nine_quarters`（内部链 69 件抽样零 sorry） |
| **等式 ω(F;1,1,1) = 9/4（每域, 含下界）+ α(F)=1/2 + 矩形闭公式** | 对照件 F1（sorried） | ⏳ 内部交付位置未定位（F4）——**若内部库无 ω ≥ 9/4, 则「精确指数/Θ(n^2.25)/驳 ω=2」的宣传口径未被形式化承载** |
| 「Lean verification passes」 | 内部审查 | ✅ 但对照件含 3 sorry（lakefile 将对照件入构建）——「通过」指内部库可编译 + 对照挑战由比较器另行核验, **非零 sorry 口径**（与 Alpöge 仓库 0-sorry 形态不同, 不可混比） |

[未验证·路线推测]: 下界 ω ≥ 9/4 的内部交付可能在 AuxiliarySeparation/Spectrum/Obstruction.lean
（谱障碍 → 分离 → 下界的形态）或 Duality/——待网络恢复取余 440 件后复查。

## 四、W-筛网四网应用（对 ω=9/4 结果本身）

| 网 | 判读 |
|---|---|
| W1 证书可枚举 | ✅ Numerical/ 8 件 = 数值证书的 Lean 内封存（先算后验同构）; Farkas 的有理证书提取 = 分离的枚举承证 |
| W2 共轭可承证 | ✅ `AuxiliarySeparation/Character/Symmetrization.lean` 等字符/对称件——张量层次的对称承证 |
| W3 正性可定位 | ✅ **F7: Farkas 锥对偶 + 渐近谱**——下界的正性来源显式定位在锥分离（与本仓库 W3 的 Schwarz 骨架同构: 谱上的正性 → 指数界） |
| W4 非循环 | ⏳ 对照件 sorried-by-design 是**显式的未证挑战**（诚实形态, 与 Alpöge 的 anyGeometry 隐性空真**相反**）——非循环性取决于内部链是否蕴含对照件, 待蕴含校验器核查 |

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
