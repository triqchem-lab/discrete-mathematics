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
