# 矩阵乘法指数线——GF(3) 下界与指数机制镜像（研究立项书，2026-11-26）

> 用户 2026-11-26 定案立项。两条线：**A** = ⟨3,3,3⟩ over GF(3) 的下界推进（外部计算 + 证书核对）；
> **B** = exponent/特征机制的库内镜像（陈述层 → 定理）。两线在「证书核对内核化」会合。
> 依据：审计 §L（文献现状图，arXiv 编号可查）、§K/K.1（构造链与定价层的域依赖判定）、
> M16–M19（PROVEN §十五–十八）。

## 立项 A：⟨3,3,3⟩ over GF(3) 的下界推进

**目标（可判定）**：拿到 GF(3) 上 3×3 双线性复杂度（张量秩）的**机器可查下界证书** ≥ 20（基础）/
≥ 21（进阶）。若 ≥ 22：GF(3) 精确秩问题收缩到「22 vs 23」。
**现状**：任意域 ≥ 19（Bläser 2003, «On the complexity of the multiplication of matrices of small formats»: R(⟨n,m,n⟩) ≥ 2mn + 2n − m − 2, m ≥ n ≥ 3; n = m = 3 即 19。陈述与出处 2026-11-28 按 arXiv:2603.07280v11 引言核对, 此前本文件写的「2n²+n−2」公式记错, 数值与年份是对的）；F₂：19 → 20（arXiv:2603.07280 Wang 框架，
机器可查证书）→ 21（arXiv:2609.06725，限制界 + 陪集分析 + 穷举）；**F₃ 的 ⟨3,3,3⟩ 未见任何声明——开口**；
同一框架已解 F₃ 的 ⟨2,3,3⟩ = 15（精确）。

| # | 任务 | 完成判据 | 依赖 | 状态/风险 |
|---|---|---|---|---|
| A-T1 | 获取 Wang 框架实现（2603.07280 的代码/证书格式） | 代码在手的运行记录入册；**或**「无公开实现」结论入册并切换到「按论文复现 DP」子立项（预算另评） | — | ✅ **2026-11-26 收口：口径锁定「获取」**——PDF 解压流扫描命中 `github.com/wcgbg/tensor-rank-lower-bound`（C++/bazel, 874 文件: `certs/` 408 份证书(.btp+.pb.txt)/`search/`/`core/`/`verifier/`/`problems/`; Zenodo DOI 10.5281/zenodo.20752782）。矩阵证书**只有 F₂**（q02_n222/n223/n224/n233/n324）；**无 F₃ 矩阵证书** ⇒ A-T3 = 自跑 F₃ 搜索。证书格式 = protobuf 文本(.pb.txt) |
| A-T2 | F₂ 复验 | 重验 2603.07280 的 q02_n333（F₂ ⟨3,3,3⟩ ≥ 20）证书 + 2609.06725 的 ≥ 21（后者证书未公开，独立检索） | A-T1 | ✅ **2026-11-27 收口**：**独立 Python 核对器全量 496/496 轨道通过**——flatten 14 + forced 14 + degenerate 230 + backtracking 238（含终轨道 ≥ 20），两次全量套件独立 OK（4133s + 4139s）+ 负控制（篡改 orbit-300 声明 +7 → 精确转红 claim 24 > proved 17）✓。调试中用 C++ probe（shim 编译信任基）逐组合对拍定位两个移植 bug（T1 打包跨步提取、query 群作用方向）。工具 = `engineering/wang_cert_check.py` + `engineering/tests/test_wang_cert_check.py`（7 项，WANG_FULL=1 门控全量） |
| A-T3 | F₃ 实例化 | 3×3 张量 + 对称群参数喂框架；产出 GF(3) 下界证书，**或**预算/轨道爆炸的边界记录入册 | A-T2 | ✅ **2026-11-27 收口: 机器可查证书 `engineering/wang_f3ext/certs/matrix_q03_n333_v1.{pb.txt,btp}`——GF(3) 上 ⟨3,3,3⟩ 的秩 ≥ 17**。三重核验: 框架 C++ verifier OK; 独立核对器（Python + 两个独立 C 内核）736/736 轨道 OK（flatten 15 + forced 2 + backtracking 339 + degenerate 380）; 负控制精确转红。**枚举不爆炸**（736 轨道 / 22 s, 完整性经轨道大小守恒逐维精确验证）。**但 17 < 域泛型已知的 19——这份证书没有刷新 F₃ 的下界**; 差距来自预算与搜索空间（F₂ 那份用满 2^32 + 1e7 步; F₃ 每维极小约束数约 2.5–3 倍、每次查找贵一个量级）。完整记录见审计 §M。**续跑 v2（2026-11-27, 1e7 步全程, 52,497 CPU 秒）: 53 条中间轨道的界上涨（dim 4 有 21 条到 14, dim 3 有 32 条到 15）, 终界仍是 17**——涨不动的因素不止预算, 还有回溯搜索的结构（审计 §M.10、`wang_f3ext/README.md` §5.3）。同日搜索层再加速（`Get` 的 NEON 批量内核; 回溯搜索去重键 + 紧凑缓存 + 扇出存储, 轨迹逐字节不变; 按目标维度实测: dim 5、1e6 步 CPU 1813 → 835 秒, dim 4、1e5 步 860 → 688 秒、扇出 8 → 115 秒; 其间有两版曾让搜索变慢、还有一个缓存淘汰的 bug 让重开的续跑卡了五个多小时, 均已更正入册）, 续跑 v3（2026-11-28 凌晨）第四次跑完: dim 3 有 2 条轨道 14 → 15, **终界仍 17**, dim 2 一张没动; 三重验证全过 [实测]。dim 2 在 3 倍步数下一张没动; 更大步数能否推动 dim 2 [未验证·路线推测] |
| A-T4 | 证书核对移植（两轨） | 证书核对器：Python（零依赖）+ 三进制 VM（TriRV）双轨通过；负控制（篡改证书一位，必须转红）——M17 三轨纪律的复用 | A-T3 | **Python 轨 ✅**: `wang_cert_check_fq.py` 对 F₃ 证书 736/736 通过 + 负控制精确转红; 其中 forced product 与回溯重放各有一个**独立的 C 内核**（`forced_fq.c`、`bt_fq.c`; 回溯重放的纯 Python 路径对 1e7 步的搜索不可行, 已与内核交叉验证）。严格说「零外部依赖」是「零第三方依赖 + cc」——两个内核由测试按需编译。TriRV 轨未做（可选增量） |
| A-T5 | Agda 内核化（远期） | 证书的核对性陈述入 `WeightedRankLE₃`/限制界语言（M19 的谓词层），exit=0 | A-T4, B-T2 | 大；先陈述层后证明 |
| 里程碑 | ≥ 20 ⇒ n=3 边界 19..23 收紧为 20..23；≥ 21 ⇒ 追平 F₂；≥ 22 ⇒ 22 vs 23 | PROVEN §十八 的边界改写 | — | ❌ **三档均未达到**（证书 ≥ 17; 现状仍是下界 19 < 秩 ≤ 23; PROVEN §十八 的边界不改写） |

## 立项 B：exponent/特征机制的库内镜像

**目标**：本库能**陈述**（最终**证明**）稀疏定律的有限形态与限制界机制。K.1 已判：五定律的证明是
域泛型组合学（Law 定义无域要求）——镜像无原理障碍；宪法排除 ℝ ⇒ 指数一律走 **Saving 型有限口径**
（分数 (p,q) 序替代实数指数，M16-D 先例）。

| # | 任务 | 完成判据 | 依赖 | 状态 |
|---|---|---|---|---|
| B-T1 | 稀疏加权谓词层 | WeightedRankLE₃/supportSize₃ exit=0 | — | ✅ M19（PROVEN §十八） |
| B-T2 | 限制界词汇 | rows/cols/inner（镜像 `Sparse/Model.lean:15-21`：支撑集上的行/列/内集计数）+ 支撑数 ≤ ijk + 「每个子空间里第一因子个数」的限制陈述（2609.06725 的证明对象）exit=0 | B-T1 | ✅ **M20**（`TensorRankRestrictGF3.agda` 115 行, 2026-11-26, PROVEN §十九）：suppRows/suppCols/suppInner + sumℕ-const/one + 全 T₁ 支撑数 = n³ + ★ weighted-zero（0 项分解 ⟹ w ≡ T₀）；陪集/子空间分析与熵词汇（conditional/premium）未镜像 |
| B-T3 | 稀疏定律有限口径 | DensityBound/CellBound/DegreeBound 的 Saving 型翻译：陈述件 exit=0（无居民，边界标注——K.1 判定的直接应用） | B-T2 | ✅ **M21**（`TensorRankSparseLawsGF3.agda` 393 行, 2026-11-27, PROVEN §二十）: 三条定律写成「对每个下斜率 p/q 的纯 ℕ 不等式」`|U|^q·(IJK)^p ≤ C^q`——`DensityBound₃` / `DegreeBound₃` 完整; **`CellBound₃` 只有平方输出集实例**（一般 \|u\| 下 Lean 的 short 给出实数边长, 格式非整数; 证明核心 width 是熵型实数量——边界标注）。衔接定理: ★ lower-slope-boundary（下半 ⟹ 方格式下斜率 3/4）、★ upper-slope-strassen（Strassen ⟹ (2,2,2) 上斜率 15/16）、★ upper-lower-slope（上 ≥ 下）、★★ degree-law-boundary（`支撑数⁴·n⁹ ≤ (432·n³·r)⁴`） |
| B-T4 | exponent 有限代理 | 在 (p,q) 分数对上定义 exponent 的离散代理（Saving 上的 sup/inf 型构造）并与 Saving₃ 单调性衔接；定理 exit=0 | B-T3 | ✅ **主体完成（随 M21, PROVEN §二十）**: 代理已定义——`LowerSlopeᵣ`（每个幂的每个分解 ≥ 体积^{p/q·幂}）与 `UpperSlopeᵣ`（每个幂存在分解 ≤ 体积^{p/q·幂}）, 与 ω₃-boundary / Strassen 的衔接已证（★ lower-slope-boundary、★ upper-slope-strassen）, ★★ **saving→upper-slope**（`RankLE₃ n r` + `r^q < n^p` ⟹ `UpperSlopeᵣ n n n p (3q)`）把 `Saving₃` 的单尺寸见证接进斜率语言。非空性见证 `upper-slope-one`（仅平凡格式 (1,1,1)）。**未做**: 一般格式的 schoolbook 非空性（需尺寸相加的直和机制, 库内只有尺寸相乘的 `rank-mul`）、与 Lean `exponent` 的等价（外部, 需 ℝ）。ℝ 被宪法排除, 这是口径关键 |
| B-T5 | tag-fiber 计数（定价层 ℕ 镜像） | `tag_count_fiber`/`meanTag` 一族的 ℕ 版；服务上界方向 | 独立 | 大；可后置 |
| B-T6 | （远期）Bläser 2mn+2n−m−2 的镜像（n = 3 的实例：`RankLE₃ 3 r → 19 ≤ r`，陈述已在 M22 `bläser₃-boundary`） | 替换法（substitution method）的下界证明 | B-T2 | 大；多会话工程，见立项 C |

**会合点**：A-T4/A-T5 的证书核对用 B-T2 的限制界词汇——2609.06725 的证明对象正是「限制界 + 支撑轮廓」，
两线的任务在这一环是同一批定义。

## 立项 C：不靠暴力搜索的数学证明（草案，2026-11-28，用户定案「先盘点、先规划、想清楚、再尝试」）

**问题**：3×3 能不能用「代数结构闭包」（代数闭包 / Frobenius–Galois 结构 / Z[ω] 共轭）证明秩的下界，不靠搜索？

**判断（盘点与核对之后）**

1. 代数闭包路线与 Frobenius 结构**给不出比已知更强的下界**，更谈不上关闭 3×3：
   - 下界的方向是 rank_F₃ ≥ rank_F₉ ≥ rank_F̄₃。Frobenius σ 只说明张量被 σ 固定
     （Fix(σ) = GF(3)，库内 `GaloisBridge` 已证）；对分解它只给出一个对合——σ 把 rank-r 的 F₉ 分解映到另一个
     rank-r 分解——不约束 r。「本体与投影重合」在秩这个问题上的全部内容就是这一句。
   - Z[ω] 那套机制搬不到 char 3：特征 3 下 ω ≢ 1 失效（x³ − 1 = (x − 1)³；库内 `ZomegaMod3` §A），
     GF(9) 用的是 x² + 1（`GF9`），C₄ 来自 α ∈ GF(9)，不是 ω。
   - 3×3 的精确秩是公开问题（r = 21 / 22 的存在性对任何域都开放，审计 §L）。
2. 两处事实更正（本文件「现状」行、审计 §L、`TensorRankSparseGF3` 头注、PROVEN 同步改）：
   19 来自 Bläser **2003** 的 R(⟨n,m,n⟩) ≥ 2mn + 2n − m − 2（m ≥ n ≥ 3，**任意域**，是秩不是边界秩；
   Bläser 1999 给的是 (5/2)n² − 3n，对 n = 3 更弱）。
   搜索得到的 17 是较弱的证书，与 19 不矛盾；「19 来自代数闭域上的 secant variety / 边界秩」的说法与
   arXiv:2603.07280v11 引言不符。

**盘点（本地库，2026-11-28）**

| 类别 | 模块 | 状态 |
|---|---|---|
| 秩分解谓词与见证 | `TensorRankGF3`（RankLE₃、rank-strassen）、`TensorRankLadermanGF3`（23 项）、`TensorRankPowGF3`、`TensorRankCircuitGF3` | ✅ 内核证 |
| 下界 | `TensorRankFlattenGF3`：rank-lower，n² ≤ r（n = 3 时 **9**） | ✅ 这是库内 n = 3 唯一的下界 |
| 外部定理的陈述层 | ω₃-boundary、ω₃-upper、bläser₃-boundary（M22） | 陈述，无居民 |
| 限制界词汇 | `TensorRankSparseGF3`（M19）、`TensorRankRestrictGF3`（M20）、`TensorRankSparseLawsGF3`（M21） | ✅ 陈述层 + 衔接定理 |
| 结构引理 | `TensorRankIndexGF3`（M22）：泛型谓词、rank-pull / rank-invar / rank-restrict / rank-swap / rank-rot | ✅ |
| 特征 3 结构 | `FieldTower/GF9`（σ、Norm、Trace）、`GaloisBridge`（Fix(σ) = GF(3)）、`FrobeniusOrbit`（C₄ 相位）、`ComplexProjection`、`Zomega` / `ZomegaMod3`、`GF27`、`GF3K` | ✅ 但与张量秩线没有接口：秩谓词只在 Trit 上 |
| 工程证书 | `engineering/wang_f3ext`（≥ 17，v1–v3） | 机器可查（C 核对器），不在 Agda 内核 |

**任务表**

| # | 任务 | 完成判据 | 状态 / 风险 |
|---|---|---|---|
| C-T0 | 盘点 + 核对前提 | 本节；PROVEN §二十一 | ✅ 2026-11-28 |
| C-T1 | M22：指标集泛型谓词 + 结构引理 + Bläser 陈述 | exit=0；oracle ALL_PASS；CheckM22 | ✅ 2026-11-28 |
| C-T2 | 替换法试点：Hopcroft–Kerr，GF(3) 上 ⟨2,2,2⟩ 的秩恰为 7（r ≤ 6 的排除论证） | ✅ `TensorRankHK2GF3.rank-2x2-lower : ∀ r → RankLE₃ 2 r → 7 ≤ r`（等价于 `∀ r → r ≤ 6 → ¬ RankLE₃ 2 r`；检查件里有 `¬ RankLE₃ 2 6`），exit=0，0 postulate | ✅ 2026-11-28。三件：M24-a `TritStdlibRing`（Trit 的标准库交换环 + ring solver）、M23 `TensorRankAlgebraGF3`（切片规范化 / 切片张成计数下界 / 线性换元）、M24 `TensorRankHK2GF3`；PROVEN §二十二。**是经典证明的形式化，不是新结论**；超平面分类是一张 80 行的内核核对见证表，不是抽象证明。已关闭 `TensorRankGF3` / `TensorRankFlattenGF3` 头注自认的缺口 |
| C-T3 | Bläser 2003 在 n = 3 的实例 | `bläser₃-boundary` 有居民，exit=0 | 大；多会话 [未验证·路线推测：替换法归纳在 GF(3) 上的子空间分类有多少，要读了原文才知] |
| C-T4 | 环泛型谓词 + 标量扩张（F₃ 分解 ⟹ F₉ 分解；σ-不变） | exit=0 | 中；**不改进界**，只是把「本体 = σ-不动点」说准；做不做取决于 C-T2 / C-T3 是否需要 |
| C-T5 | Wang 证书内核化（17）：Agda 里检查 `.btp` | exit=0 | 大且不确定：1880 万个叶子在内核里逐个检查的代价没估过 |
| C-T6 | F₃ 容量–剖面探针：r = 19 的容量约束是否把假想分解逼进 Δ = 0（决定「互补幂等」恒等式值不值得形式化） | 查表件 + 验证；给出「是 / 否」之一的证据 | 探针已做（2026-11-28，用户定方向「走探针，明确不做 C-T3，至少现在不做」）：容量表 / 查表件 / 五道验证齐备，`ALL_PASS`。**主问题未决**——没找到零违规且 Σ 秩 ≥ 28 的首因子配置，也没证明不存在。PROVEN §二十三。**决定：现在不形式化幂等恒等式** |

| — | 关闭 3×3（精确秩） | — | 公开问题；不立项 |

**C-T2 执行记录（2026-11-28）**：三件全部进内核（PROVEN §二十二）。对 C-T3 的影响，只说已经站得住的部分：

- 现成可复用：`TensorRankAlgebraGF3` 的四条通用操作（丢零项、切片规范化、切片张成的计数下界、线性换元）
  与 `TritStdlibRing` 的 ring solver。它们与矩阵大小无关。
- 2×2 的证明只有一层代换（全空间 → 超平面 → K）。3×3 的框架证书（F₃，v1）有 736 个轨道（下标 0–735；`certs/matrix_q03_n333_v1.pb.txt` 数出来的）；
  Bläser 的手写证明用多少个子空间、能不能用同一套件走完，**没有读过原文，不知道**
  [未验证·路线推测]。下一步的检查动作：读 Bläser 2003 原文，列出它用到的全部子空间，再看每个子空间能否用
  `slice-normalize` + `SpanGen.bound` 处理。
- 2×2 的做法里有一处不能直接放大：超平面分类用的是「80 行见证表 + 内核归约」。n = 3 时非零泛函有 3⁹ − 1 = 19682 个，
  逐个列表的做法不现实；要么做抽象的分类证明，要么换一种参数化。[未验证·路线推测]

**C-T6 执行记录（2026-11-28）**：只说站得住的部分（PROVEN §二十三）。

- 容量约束 N(W) + L(W^⊥) ≤ r 的推导只有三行；736 个轨道的证书给出一切 W^⊥ 的下界。
  r = 19 的容量表：每条直线 ≤ 3 项、每个平面 ≤ 4 项、每个 3 维子空间 ≤ 4–6 项。
- 可复用：`engineering/wang_f3ext/standalone/orbit_lookup.cc`（「子空间 → 证书界」查表 + 完备的配置检查）与
  `engineering/wang_capacity_probe.py`（五道验证：自检 / 见证重放 / 两套完备枚举互证 / Laderman 真实分解在 r = 23 零违规 /
  L = 12 平面轨道的精确结构）。
- 实测：随机 19 点配置 665–1121 处违规（「7 维 + 恰 8 点 + L = 12」占 38%，不是唯一的来源）；
  L = 12 的平面 = 8 个非零元素全可逆的平面（K = A·span{I, N}，N 生成一份 F₂₇），占全部平面的 10.02%；
  几种结构化族与两种局部搜索都没到零。
  码表事实（未独立核验）：任何 19 点配置必有超平面含 ≥ 12 个点、必有 ≤ 6 个点线性相关。
- 没有回答的：是否存在满足全部容量约束且 Σ 秩 ≥ 28 的配置。[未验证·路线推测] 下一步若继续，
  应在规范化族里做精确搜索（约束规划 / SAT），而不是随机撒点；核对动作见 PROVEN §二十三末。

## 形式化任务重排（2026-11-28，用户「把现在的研究成果形式化，前面规划的形式化任务重新规划下」）

### 现状盘点：哪些在内核、哪些只在工程层

| 层 | 内容 | 权威 |
|---|---|---|
| **内核**（exit=0，0 postulate） | M16–M22（谓词、展平下界、幂、上界、稀疏定律、Laderman 23）、M23/M24（GF(3) 上 ⟨2,2,2⟩ 秩恰为 7）、**M25 容量引理、M26 剖面算术、M27 秩预算**（本次新增，PROVEN §二十四） | Agda 内核 |
| **机器可查证书**（不在内核） | F₃ ⟨3,3,3⟩ ≥ 17（736 轨道；框架 verifier + 独立核对器）；F₂ ≥ 20（496 轨道） | C++ / Python 核对器 |
| **探针级**（Python 驱动 + 查表件，五道验证） | r = 19 的容量表数值；L = 12 平面的结构（808,704 个）；H₀ 内部穷举；随机配置违规画像 | `wang_capacity_probe.py` |
| **文献**（未形式化） | Bläser 19；Wang F₂ ≥ 20 / 21；Yang 幂等法；Conner–Harper–Landsberg 边界秩 ≥ 17 | 摘要级（§二十三末） |

缺口（盘点时确认的）：库内 **GF(3) 矩阵秩理论不完整**——`GF3Rank` 头注自认「未给出完整 echelon 算法、未证秩在行变换下的不变性」；
M20 只镜像了支撑计数词汇，没有「落在子空间里的项数」这条限制。所以 M25 / M27 都写成不依赖矩阵秩的形状。

### 新任务表（F 系列：把探针成果形式化）

| # | 任务 | 依赖 | 状态 / 规模 / 风险 |
|---|---|---|---|
| F-T1 | **M25 容量引理**：`rank-drops`（限制后恒零的项全部丢掉）、`capacity`（沿 ι 限制后丢项）、`capacity-bound`（N + L ≤ r）、`capacity-span`（W = span g） | M22 `rank-pull`、M23 `rank-drop` / `rank-cong` | ✅ `TensorRankCapacityGF3.agda`（221 行）。哨兵：Laderman 在 (0,0) 的切片由 23 项降到 5 项（个数由内核数出）。**不改进任何下界** |
| F-T2 | **M26 剖面算术**：`profile-Δ`、`profile-param`、★★ `profiles-19`（r = 19、Σ 秩 = 27 恰五种）、`profiles-23` | — | ✅ `TensorRankProfileGF3.agda`（173 行）。纯算术，不含张量秩 |
| F-T3 | **M27 秩预算**：★★ `rank-budget : Pieces n N r (ra ρ) → n³ ≤ N` | M22、M23 `sumFin-scale`、`GF3Count` | ✅ `TensorRankBudgetGF3.agda`（372 行）。哨兵：Strassen 的 7 个首因子拆成 8 片 ⟹ 8 ≤ 8；负对照：3 片 / 7 片拼不出。结论是对「片块数」说的，不是对「矩阵秩」 |
| F-T4 | **Laderman 片块表**：由 oracle 发射 31 个秩一片块，内核里 `pieces-laderman : Pieces 3 31 23 (ra L)`，于是 `rank-budget` 给出 27 ≤ 31，与 M26 的 `laderman-not-Δ0` 接上 | F-T3 | 未做。小–中（发射脚本 + 表；拼装等式要按指标展开成 refl，M24 的 `hyper-wit` 同一做法）。核对动作：先让 oracle 打印 31 个片块并断言片块数 = Σ 秩 |
| F-T5 | **3×3（或 n×n）矩阵秩理论**：完整的 echelon、`rank` 的定义与不变性、「rank ρ ⟺ 能写成 ρ 个秩一片块」、次可加性、左乘像的维数 | — | 未做。大（M23 级）。它是 F-T6 / F-T7 的前置，也是把 F-T3 升级成「Σ_t rank(a_t) ≥ n³」的前提 |
| F-T6 | **直线容量**：对 ⟨3,3,3⟩ 的分解与首因子 a₀，落在 span{a₀} 里的项数 ≤ r − 3·rank(a₀) | F-T1、F-T5 | 未做。大。两半：用 `capacity-span`（W = span{a₀}，V = a₀ 的核）；证切片张量 tr(a₀ b c) 的下界 3·rank(a₀)（M23 `SpanGen.bound` 一类）。**不改进数字**，只是第一条带具体下界的容量约束进内核 |
| F-T7 | **平面容量**（dim W = 2）：14 个平面型各给下界 15 | F-T5、F-T6 | 未做。很大（M24 级 × 14）。建议等容量–剖面探针给出方向后再定 |
| F-T8 | **证书内核化**（= 旧 A-T5 / C-T5）：736 个轨道的证书界在 Agda 里检查 | — | 不变：大且不确定（1880 万个叶子在内核里逐个检查的代价没估过）。F-T6 / F-T7 是它的低维手工版 |
| F-T9 | **L = 12 平面的有限事实**：全可逆平面 = A·span{I, N}，808,704 个 | — | 可选、价值低（只是解释性的）。内核可算的是「没有 F₃ 特征值的 3×3 矩阵 3456 个」（3⁹ 次枚举）；平面总数 8,069,620 的枚举在内核里估计太慢 [未验证·路线推测] |
| F-T10 | **幂等恒等式** | Δ = 0 的证据 | **暂不做**（§二十三：容量是否逼出 Δ = 0 未决） |

### 旧任务的去留

| 旧编号 | 处置 |
|---|---|
| A-T4（TriRV 轨）| 可选增量，未做 |
| A-T5（内核化）| 并入 F-T8，远期 |
| B-T4 余项 / B-T5 | 不变（schoolbook 非空性、tag-fiber 计数） |
| B-T6 = C-T3（Bläser 19）| 用户已定「至少现在不做」 |
| C-T4（环泛型）| 低优先 |
| C-T6（探针）| ✅ 已做；主问题未决（§二十三）。续做方向是规范化族里的精确搜索，不是形式化 |
| 外部文档阶段 0 / 1 / 2 / 3 | 阶段 0 ✅；阶段 1（幂等）暂停 = F-T10；阶段 2（F₉ 对称族）不做；阶段 3 的「1D/2D 商界」= F-T6 / F-T7，其「容量」一半 = F-T1 ✅ |

### 推荐顺序

F-T4（Laderman 片块表：小，把 M25 / M26 / M27 三件接到一个真实分解上）→ F-T5（矩阵秩理论：基础设施）
→ F-T6（直线容量：第一条带具体下界的容量约束）→ 之后视容量–剖面探针的结论再定 F-T7 / F-T10。
每一步都不改进库内的下界数字（n = 3 仍是展平 9 + 工程证书 17；域泛型已知 19 在内核里只有陈述层 `bläser₃-boundary`）。

## 资源与纪律
- 工具：arXiv API / GitHub 检索走代理 `socks5h://127.0.0.1:10808`；Agda = `~/.local/bin/agda`；
  TriRV = `~/ai-lab/trirv`（不动 bench 现有件）；Python 零依赖 + unittest discover。
- 纪律：先算后验（oracle 先行/数值子句发射）；路线判断带核对动作或标 [未验证·路线推测]；
  散文断言指向内核定理；提交消息走文件 + `git commit -F`；顶层名查重；不推送远程。
- 进度登记：本文件 + `PROVEN.md` §十五–十八 + 审计 §K/K.1/L。
