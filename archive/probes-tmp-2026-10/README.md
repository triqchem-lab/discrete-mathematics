# 归档目录

本目录存放中间产物/探针/已废弃桥接文件——不是核心链组件，不参与编译。
每个文件保留完整内容与 git 历史，便于后期排查。

| 文件 | 原路径 | 状态 | 说明 |
|------|--------|------|------|
| _ProbeAssoc.agda | Algebra/ | 被取代 | rearrange9 原始证明（已复制到 BurauCubical）|
| IntRingSolver.agda | Algebra/ | 被取代 | ℤ→RingSolver 桥（rearrange 方法取代）|
| _ProbeSum3.agda | Cubical/ | 探针 | sum3-comm 诊断用（已由 Fin3 rearrange 方法解决）|

## 2026-10-10 List 路线归档（裁决 ⑤：主路线 = 函数表示）
LaurentBase/Canon/Distrib/MulAssoc/Norm/Polynomial/PolynomialFull/Ring/Sort/Sums 共 10 个 List 投影模块归档于此。
保留主线：LaurentCubical（cubical 函数表示）+ LaurentFn（PropEq 函数表示）。BurauRep 已迁移至 LaurentCubical。
命题事实不变（台账 Laurent.* 节点的 proven 事实继续有效），仅代码位置迁移。见 docs/decisions/数学严谨性路线选择-2026-10-10.md §⑤。

## 2026-10-10 归档撤销（裁决 ⑤ 三次修订：两路线共存）
Laurent List 族 10 模块已移回 src/Sovereign/Algebra/（构造主义 vs 定义严格性两维度共存，List 代码不碍主链）。本目录恢复原状：仅余 Hensel2Side-wip / IntRingSolver / _ProbeAssoc / _ProbeSum3 / probes-tmp 等既有件。见 docs/decisions/数学严谨性路线选择-2026-10-10.md §⑤ 修订。

## 2026-10-11 草稿整理批收尾（归档定性终表——零删除）
**定性口径**：归档件=历史成果保全（不进门禁不参与编译）；本节为逐件定性终表。

### 顶层件
| 文件 | 规模 | 定性 | 处置 |
|------|------|------|------|
| Hensel2Side-wip-20261009.agda | 355 行 | **被取代**（Hensel2Side 已在 src 收官——Hensel 族 28/28，回执 `c281a271`） | 保留归档（历史 WIP 面） |
| IntRingSolver.agda | 34 行 | 被取代（rearrange 方法取代 ℤ→RingSolver 桥） | 保留归档 |
| _ProbeAssoc.agda | 96 行 | 被取代（rearrange9 原始证明→BurauCubical） | 保留归档 |
| _ProbeSum3.agda | **0 行（空件）** | 纯残件 | 保留归档（git 历史见证——零删除纪律） |

### probes-tmp/ 子件（31 件三族）
| 族 | 件 | 定性 |
|----|----|------|
| **诊断探针族** | Probe9/ProbeA-J/ProbeAssoc/comm_lines/_Probe 系 | 诊断用探针——sum3 族关联**历史假绿事故**（sum3-comm「报全绿实有类型错」案）；问题已由 Fin3 rearrange 方法在 src 解决（见裁决 ⑤ 文档） |
| **工程工具族** | f3_base/f3_append/f3final/ff-matrix/ff-bidi/ff-plan/ff-smoke/ff-shoot.sh/burau_oracle.py/zomega_ring_oracle.py/verify_chain.py/gen_sum3/gen_swaps/fixv.py | Python oracle/生成器脚本（先算后验证轨道的工程件） |
| **被取代件** | BubbleLemmas/bubble_lemmas（→_PPI5g bubble 面）/fin3_final（→Base/Fin3） | 保留归档 |

### ProbeJ.agda 洞面定性（FinitenessZoo 归档先例口径）
`sum3-comm f = {!!}`（:14）= **WIP 草稿洞**（诊断探针的合法草稿态）——**无形式化保证**：本件不构成 sum3-comm 的证明；命题本体已在 src 以 Fin3 rearrange 路线解决。文件内注记已加。
