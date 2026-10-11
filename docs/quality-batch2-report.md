# QUALITY.batch2-algebraic-geometry 质量审计报告（2026-10-11）

> 域：Jacobian（Algebra/Jacobian 17 件）+ Hodge（Problem/Hodge 30 件）+ BSD（Problem/BSD 10 件）= **57 文件**。
> 口径：batch0 机械面（多行签名容错）+ 四问抽样 8 重点件深读（低活动/thm=0/委托嫌疑优先）+ batch0 异常清单对账。

## 一、机械面（全扫 57）
| 域 | 文件 | post | hole | 活动/定理 | 链深 |
|---|---|---|---|---|---|
| Jacobian | 17 | **0** | 0 | 总 act 1534 / thm 228（≈6.7） | 0 真违规 |
| Hodge | 30 | **0** | 0 | 总 act 506 / thm 113（≈4.5） | 0 |
| BSD | 10 | **0** | 0 | 总 act 47 / thm 38（≈1.2） | 0 |

**零 postulate 零 hole 全域** ✓；batch0 post>0（25 件）对账：**本域零命中**（中吕/Entanglement/TQ10 等全在他域）。

## 二、四问抽样（8 重点件——活动=0≠空壳警示内置）
| 件 | 剖面 | 四问定判 |
|---|---|---|
| `jac_DiscreteJC`（325 行/8 sig/thm 0/act 5） | 单行委托/见证型（`formal-passes`/`F-blind`/`table-fails` 委托链） | **A−（委托型）**——上游 jac_Discrete 已证，本件为见证装配 |
| `BSD_GF243`（38 行/thm 0/act 1） | q3/t5*/e* 数值表 + refl 核对（GF(243) 迹计算面） | **B+（数据+核对件）**——BSD 计算层诚实形态；同族 GF27/GF81 同判 |
| `Hodge_L3`（39 行/sig 0） | 纯注释/状态陈述件 | **C（已注记）**——B014 批已入「对账表型」诚实边界 ✓ 不重复计缺陷 |
| `DeligneHodge`（27 行） | z-dim≡h-dim=1 refl（1 维玩具实例） | **C⁺（实例核）**——deligne-holds 为实例非定理；头注边界待补一句（轻） |
| `GraphMorseInstance`（86 行/act 1） | β/m 数据 + dimH-graph3 导入对账（Morse 不等式实例） | **B+（数据+对账）** |
| `FreeAbImSubsetPlane`（70 行/act 28） | w₃/sum₃ 定义 + 承载件（thm 0 = 定义层） | **对象级形 ✓**（定义件非空壳） |
| `jac_Matrix`/`jac_CRTDet`/`jac_PermDet`（725/501/393 行） | act 424/359/196——深度主力 | **A（实证层）**（深度审核同判） |
| `FreeAbH0`（87 行/act 82） | 高密度核对件（aug-∂₁-zero 先例复用面） | **A/B+**（复用型密集） |

## 三、缺陷清单（file:line）
1. `Problem/Hodge/DeligneHodge.agda` 头部——补一句实例核边界（「1 维玩具实例对账，非 Deligne-Hodge 一般定理」）——**轻**；
2. `Problem/BSD/BSD_GF243/27/81` 头注——数值表定位句（「GF(3^k) 迹计算面数据+核对」）可补六段式头（B015 覆盖面外，同 B013/B014 批型）——**轻**；
3. `jac_DiscreteJC` 单行委托注记可升正式头（「见证装配层」定位）——**轻**。
（无内容级缺陷——零空壳零 postulate 零洞。）

## 四、定判汇总
- **A/B+ 实证层 ≈ 49 件**（Jacobian 深度主力 + Hodge 机件族 + BSD 大件）；
- **数据/核对/委托型 ≈ 7 件**（BSD 迹表族 3、GraphMorseInstance、DeligneHodge、jac_DiscreteJC、Hodge_L3）——均为诚实形态非空壳；
- **C 级 1 件**（Hodge_L3，已注记对账表型——沿 B014 判）；
- **处置**：3 条轻缺陷入「补文档」工单（可并 B015 或 B014 后续）；无降级项。

## 附录：跨批对账
- QA.bsd（两域复核）：BSD 大件 A/B 实证 ✓（本批维持）；
- batch0 异常三类：post>0 本域 0｜hole>0 0｜活动=0 且 sig>0 **0**（最低 act=1：GraphMorseInstance/Hodge_L3/BSD_GF 族——均为数据/对账形非空壳）；
- 前审计 D 系列：无本域残项。
