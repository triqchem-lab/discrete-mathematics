# QUALITY.batch1-abstract-algebra 质量审计报告（2026-10-11）

> 抽样框：Algebra 树（含 GroupTheory 子目录）258 模块 / 66,633 行（batch0 底料口径；M9 旧口径 82+29 为子集）
> 口径：机械全扫 + 语义抽样 20+；四问人工判（活动=0 优先）；⚠ 活动=0≠空壳（委托型 IntByParts 先例）

## 一、机械面（全扫 258）
| 维度 | 结果 |
|---|---|
| postulate | **1 件**（CartanMatrix post=2）——batch0 对账 ✓ |
| hole | **0** ✓ |
| 活动/定理比 | 树均 4.2（全库 3.7 之上） |
| 链深 | **0 真违规**（3 处扫描命中全为论证档/合规形，见 §四） |

## 二、四问抽样（语义 20+，重点件逐条）
| 件 | 剖面 | 四问定判 | 处置 |
|---|---|---|---|
| **HenselMigration ×13**（各 37 行/thm=4/活动 0） | mig-root-* 见证 + 非根委托（HenselMod* 族已证件） | **B+ 委托/见证型**（G1' 迁移批生成件——非空壳；活动 0 = 单行委托体不触发活动标记） | 如实留档；头注统一升级可批量 |
| **DiscreteJacobi**（25 行） | `theorem = fst (detNonzero↔bij F) dn`——**单行委托** | **A- 委托型**（上游 jac_Pigeonhole 已证；真定理非空壳） | 留档 |
| **BraidGroup**（67 行） | B3 presentation record（对象级） | **对象级 ✓**（kind:object proven 在案） | 无 |
| **LaurentBase**（75 行/sigs=10/thm=0） | 类型定义层（base-unify 归一后的唯一定义处） | **对象级 ✓** | 无 |
| **Matrix2**（84 行/thm=0） | 类型定义层（B.Mat2 wire 对象） | **对象级 ✓** | 无 |
| **CartanMatrix**（post=2） | Kac-Moody presentation 关系层 | **C+ 定义层**（关系入定义候选——B3 先例适用） | 见 §三① |
| LaurentRingLaws/BurauCubical/Jacobian 等链深件 | 论证档范式/合规形 | ✓ 非违规 | 无 |

## 三、缺陷清单（file:line）
1. **`Algebra/CartanMatrix.agda:77-83`**——postulate ×2（`hh-rel`/`ef-rel`）：
   - 性质 = **presentation 关系**（[h_i,h_j]=0 / [e_i,f_j]=δ_ij h_i）⇒ 豁免精化判据正解②「关系入定义」候选（record 展示定义：h/e/f 生成元 + 关系字段 + 结构公理，B3 先例）；
   - ⚠ **陈述层简化边界**：`ef-rel` 注释自认「简化：δ_{ij} 的情况」——`e i · f j ≡ zero` 是**零化截断形**（标准 Kac-Moody 为 δ_ij h_i）——建议 header 显式标注「截断形 presentation（非标准 Kac-Moody 关系）」防误引；
2. **`Algebra/HenselMigration*.agda`（13 件）**——生成件头注统一升级（六段式第三维：定位句/背景/原则/包含——一改全改批）；
3. 链深 3 处扫描命中经行号核全为合规/论证档（BurauCubical 附录14 范式件 ×3、jac_Matrix 重组后 2-2、PermDet 2-3、RingLaws ≤3）——**非缺陷**（防假阳性二度兑现）。

## 四、定判汇总
| 级 | 件 | 说明 |
|---|---|---|
| A/B（实证） | 大部（树均活动/定理 4.2） | 含委托型 14 件（13 迁移 + DiscreteJacobi） |
| 对象级 | BraidGroup/LaurentBase/Matrix2 等 | 定义层合法（kind:object 口径） |
| C+（定义层待升级） | CartanMatrix | 关系入定义 + 截断形标注 |

**与 batch0 异常清单对账**：post>0 清单 ✓ 1 件核毕（kind = presentation 关系入定义候选）；活动=0 清单 ✓ 16 件全判（委托/见证/对象型——零真空壳）；hole ✓ 0。

**处置建议**：① CartanMatrix 关系入定义（B3 范式，~1 批）+ ef-rel 截断形标注；② HenselMigration 13 件头注批（轻）；③ 其余留档。
**验证点**：① 四维表+缺陷清单+定判 ✓ ② batch0 对账 ✓ ③ 零源码改动 ✓

## 附录：与前次批1 审计（149 文件口径）对账
前审计四发现逐条核实（2026-10-11 实测）：
- D1「DivisorLattice 4 引理各 36 case 超阈」→ **已消/表述过时**：meet-comm/join-comm @:235-239 现为 `cong₂ _,_ (min3-comm a c) (min2-comm b d)` 结构化委托形（非穷举）；
- D2「jac_Matrix:203 注释漂移」→ **已修**：现注「[策略B] 结构化（已替换旧 6561-case 穷举）」✓；
- D3「jac_DiscreteJC 洞 1」→ **已填**（剥注释 hole=0 实测）；
- D4「重复名判重」→ **已结**（dup-names 批 904 组三型判毕，Variation 对证伪）。
⇒ 前审计四发现全数处置或过时；本报告为**当前态**审计。口径差异注：149 vs 258 = GroupTheory 子目录计入与探针面差异。
