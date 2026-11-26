# 矩阵乘法指数线——GF(3) 下界与指数机制镜像（研究立项书，2026-11-26）

> 用户 2026-11-26 定案立项。两条线：**A** = ⟨3,3,3⟩ over GF(3) 的下界推进（外部计算 + 证书核对）；
> **B** = exponent/特征机制的库内镜像（陈述层 → 定理）。两线在「证书核对内核化」会合。
> 依据：审计 §L（文献现状图，arXiv 编号可查）、§K/K.1（构造链与定价层的域依赖判定）、
> M16–M19（PROVEN §十五–十八）。

## 立项 A：⟨3,3,3⟩ over GF(3) 的下界推进

**目标（可判定）**：拿到 GF(3) 上 3×3 双线性复杂度（张量秩）的**机器可查下界证书** ≥ 20（基础）/
≥ 21（进阶）。若 ≥ 22：GF(3) 精确秩问题收缩到「22 vs 23」。
**现状**：域泛型 ≥ 19（Bläser 2003，2n²+n−2 在 n=3）；F₂：19 → 20（arXiv:2603.07280 Wang 框架，
机器可查证书）→ 21（arXiv:2609.06725，限制界 + 陪集分析 + 穷举）；**F₃ 的 ⟨3,3,3⟩ 未见任何声明——开口**；
同一框架已解 F₃ 的 ⟨2,3,3⟩ = 15（精确）。

| # | 任务 | 完成判据 | 依赖 | 状态/风险 |
|---|---|---|---|---|
| A-T1 | 获取 Wang 框架实现（2603.07280 的代码/证书格式） | 代码在手的运行记录入册；**或**「无公开实现」结论入册并切换到「按论文复现 DP」子立项（预算另评） | — | ✅ **2026-11-26 收口：口径锁定「获取」**——PDF 解压流扫描命中 `github.com/wcgbg/tensor-rank-lower-bound`（C++/bazel, 874 文件: `certs/` 408 份证书(.btp+.pb.txt)/`search/`/`core/`/`verifier/`/`problems/`; Zenodo DOI 10.5281/zenodo.20752782）。矩阵证书**只有 F₂**（q02_n222/n223/n224/n233/n324）；**无 F₃ 矩阵证书** ⇒ A-T3 = 自跑 F₃ 搜索。证书格式 = protobuf 文本(.pb.txt) |
| A-T2 | F₂ 复验 | 重验 2603.07280 的 q02_n333（F₂ ⟨3,3,3⟩ ≥ 20）证书 + 2609.06725 的 ≥ 21（后者证书未公开，独立检索） | A-T1 | ✅ **2026-11-27 收口**：**独立 Python 核对器全量 496/496 轨道通过**——flatten 14 + forced 14 + degenerate 230 + backtracking 238（含终轨道 ≥ 20），两次全量套件独立 OK（4133s + 4139s）+ 负控制（篡改 orbit-300 声明 +7 → 精确转红 claim 24 > proved 17）✓。调试中用 C++ probe（shim 编译信任基）逐组合对拍定位两个移植 bug（T1 打包跨步提取、query 群作用方向）。工具 = `engineering/wang_cert_check.py` + `engineering/tests/test_wang_cert_check.py`（7 项，WANG_FULL=1 门控全量） |
| A-T3 | F₃ 实例化 | 3×3 张量 + 对称群参数喂框架；产出 GF(3) 下界证书，**或**预算/轨道爆炸的边界记录入册 | A-T2 | 🟡 **进行中（2026-11-27）**: F₃ 扩展 + 手工构建已入库（`engineering/wang_f3ext/`, 提交 d7016315; bazel 在本机构建崩溃, 走 clang++ 直编 + 垫片）。**枚举不爆炸**: 736 轨道 / 22.4 s / 200 MB, 完整性经轨道大小守恒独立检验（10 个维度 Σ\|orbit\| = 高斯二项系数逐维精确相等）。**速度边界（实测）**: 框架的通用 F_q 路径没有 F₂ 那样的位打包快路径, forced product 每次迭代约 20 µs——3.87 亿次枚举要 16 分钟/投影位（8 线程）; 大预算（log2 = 32）把 dim 7 的三条轨道从 10–11 提到 12, 但 dim 6（84 条轨道 × ≤3 投影位）按此速度最坏需数十小时 ⇒ 分阶段: 高维用大预算、低维用中预算。下界搜索运行中, 结果待 verifier + 独立核对后入册 |
| A-T4 | 证书核对移植（两轨） | 证书核对器：Python（零依赖）+ 三进制 VM（TriRV）双轨通过；负控制（篡改证书一位，必须转红）——M17 三轨纪律的复用 | A-T3 | **Python 轨 ✅**（随 A-T2 完成：独立核对器 + 负控制精确转红）；TriRV 轨待做（.btp 二进制 proto 解码 + DFS 重放的 ternary 移植，可选增量） |
| A-T5 | Agda 内核化（远期） | 证书的核对性陈述入 `WeightedRankLE₃`/限制界语言（M19 的谓词层），exit=0 | A-T4, B-T2 | 大；先陈述层后证明 |
| 里程碑 | ≥ 20 ⇒ n=3 边界 19..23 收紧为 20..23；≥ 21 ⇒ 追平 F₂；≥ 22 ⇒ 22 vs 23 | PROVEN §十八 的边界改写 | — | — |

## 立项 B：exponent/特征机制的库内镜像

**目标**：本库能**陈述**（最终**证明**）稀疏定律的有限形态与限制界机制。K.1 已判：五定律的证明是
域泛型组合学（Law 定义无域要求）——镜像无原理障碍；宪法排除 ℝ ⇒ 指数一律走 **Saving 型有限口径**
（分数 (p,q) 序替代实数指数，M16-D 先例）。

| # | 任务 | 完成判据 | 依赖 | 状态 |
|---|---|---|---|---|
| B-T1 | 稀疏加权谓词层 | WeightedRankLE₃/supportSize₃ exit=0 | — | ✅ M19（PROVEN §十八） |
| B-T2 | 限制界词汇 | rows/cols/inner（镜像 `Sparse/Model.lean:15-21`：支撑集上的行/列/内集计数）+ 支撑数 ≤ ijk + 「每个子空间里第一因子个数」的限制陈述（2609.06725 的证明对象）exit=0 | B-T1 | ✅ **M20**（`TensorRankRestrictGF3.agda` 115 行, 2026-11-26, PROVEN §十九）：suppRows/suppCols/suppInner + sumℕ-const/one + 全 T₁ 支撑数 = n³ + ★ weighted-zero（0 项分解 ⟹ w ≡ T₀）；陪集/子空间分析与熵词汇（conditional/premium）未镜像 |
| B-T3 | 稀疏定律有限口径 | DensityBound/CellBound/DegreeBound 的 Saving 型翻译：陈述件 exit=0（无居民，边界标注——K.1 判定的直接应用） | B-T2 | ✅ **M21**（`TensorRankSparseLawsGF3.agda` 393 行, 2026-11-27, PROVEN §二十）: 三条定律写成「对每个下斜率 p/q 的纯 ℕ 不等式」`|U|^q·(IJK)^p ≤ C^q`——`DensityBound₃` / `DegreeBound₃` 完整; **`CellBound₃` 只有平方输出集实例**（一般 \|u\| 下 Lean 的 short 给出实数边长, 格式非整数; 证明核心 width 是熵型实数量——边界标注）。衔接定理: ★ lower-slope-boundary（下半 ⟹ 方格式下斜率 3/4）、★ upper-slope-strassen（Strassen ⟹ (2,2,2) 上斜率 15/16）、★ upper-lower-slope（上 ≥ 下）、★★ degree-law-boundary（`支撑数⁴·n⁹ ≤ (432·n³·r)⁴`） |
| B-T4 | exponent 有限代理 | 在 (p,q) 分数对上定义 exponent 的离散代理（Saving 上的 sup/inf 型构造）并与 Saving₃ 单调性衔接；定理 exit=0 | B-T3 | **部分 ✅（随 M21）**: 代理已定义——`LowerSlopeᵣ`（每个幂的每个分解 ≥ 体积^{p/q·幂}）与 `UpperSlopeᵣ`（每个幂存在分解 ≤ 体积^{p/q·幂}）, 与 ω₃-boundary / Strassen 的衔接已证。**未做**: 与 `Saving₃` 本身（单尺寸严格见证）的直接衔接、上斜率的 schoolbook 非空性（需一般格式的 schoolbook 矩形分解）、与 Lean `exponent` 的等价（外部, 需 ℝ）。ℝ 被宪法排除, 这是口径关键 |
| B-T5 | tag-fiber 计数（定价层 ℕ 镜像） | `tag_count_fiber`/`meanTag` 一族的 ℕ 版；服务上界方向 | 独立 | 大；可后置 |
| B-T6 | （远期）Bläser 2n²+n−2 镜像 | 替换法（substitution method）的下界证明 | B-T2 | 大；公开问题级下游 |

**会合点**：A-T4/A-T5 的证书核对用 B-T2 的限制界词汇——2609.06725 的证明对象正是「限制界 + 支撑轮廓」，
两线的任务在这一环是同一批定义。

## 资源与纪律
- 工具：arXiv API / GitHub 检索走代理 `socks5h://127.0.0.1:10808`；Agda = `~/.local/bin/agda`；
  TriRV = `~/ai-lab/trirv`（不动 bench 现有件）；Python 零依赖 + unittest discover。
- 纪律：先算后验（oracle 先行/数值子句发射）；路线判断带核对动作或标 [未验证·路线推测]；
  散文断言指向内核定理；提交消息走文件 + `git commit -F`；顶层名查重；不推送远程。
- 进度登记：本文件 + `PROVEN.md` §十五–十八 + 审计 §K/K.1/L。
