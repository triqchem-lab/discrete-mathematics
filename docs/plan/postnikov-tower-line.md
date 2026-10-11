# Postnikov 塔线（任务书 6.1）——研究与任务计划

> 建立：2026-10-11｜台账骨架：`Taskbook-6.1-postnikov-tower` + PT-1..PT-5（proof_dag plan 已落盘，全 pending）
> 出处：M. M. Postnikov, Труды МИАН СССР 46 (1955), 3–158——Postnikov 塔 + Postnikov 不变量（「Postnikov 系统」）

## 一、任务书口径与框架关系
- **核心主张**：空间同伦型 ⟶ 纤维塔逐层逼近（纤维 = Eilenberg-MacLane 空间 K(πₙ,n)）+ 上同调不变量（kₙ）分层代数化；
- **框架关系**（任务书原文）：Postnikov 塔 = 连续空间的「离散分解」；T⁶ 格点 = 离散空间的「有限生成」——**分界 = 无限同伦群 vs 有限群 (Z/3Z)⁶**；
- **切入点**：`PostnikovTower : (X : Space) → ℕ → Space` + `postnikovInvariant`；250-350 行；P3。

## 二、本地现状（审计对账 2026-10-11）
| 机件 | 状态 | 回执 |
|---|---|---|
| π₁ᵈ（Loop/AHomotopy 商型） | ✅ A 级 | b2-群线 |
| π₂ᵈ := π₀(Ω²ᵈ)（骨架） | ✅ proven | `cd2a2a0d` |
| Ω³ 填充理论（Ω3Walk/fill-tri） | ✅ 首批 | `cd2a2a0d` |
| Sⁿᵈ 组合球面 + DHomotopy + 商型 + 柱体 | ✅ B1-B5 全落地 | `ebd78a1e`..`b725294d` |
| PostnikovTruncation（disp 1-截断类比） | ✅ A 级（**诚实标注：类比非真身**） | `854df5b8`/`e6a1250b` |
| StongCore（beat point 构造性核） | ✅ 核闭合档 | QA batch4 |
| **PostnikovTower 塔结构 / k 不变量** | ❌ **未开线**（本计划对象） | — |

**理论红线**（审核六错位对照在案）：指标阶数以标准形为准（kₙ ∈ H^{n+1}(X_{n-1};πₙ)）；纤维化≠纤维丛≠Grothendieck；K(G,n) 非有限偏序集；Stong 核心≠塔终止；T⁶ 偏序显式（linPoset 语境）。

## 三、路线选择：Ωⁿ 迭代形为主 + EM 对照形可选
- **主线（PT 系列采用）**：Ωⁿ 迭代离散形——纤维的离散对应 = **Ωⁿᵈ 迭代循环空间**（零 K(G,n) 重机件；n=1 一致性四验已证）；
- **对照形（未开线，保留）**：EM 空间抽象接口（复用 `Cubical.HITs.EilenbergMacLane`/agda-unimath——不从零建）——作为「π₂ᵈ=经典同伦类对齐定理」的对侧定义（立界 1-2 批，PT-4 的 kₙ 与经典 k-不变量的桥在此）。

## 四、任务分解（台账 PT 系列——全 pending）
| 义务 | 内容 | 验证 | 估 |
|---|---|---|---|
| **PT-1** | 基础对账：同伦论基础的本地机件清单（不重证） | grep 清单+回执对账 | 轻 |
| **PT-2** | `PostnikovTower X n`：Xₙ 阶段 + 映射 + 截断性质 πᵢ(Xₙ)=0(i>n) 离散形 | 探针绿 + disp 对账 | 60-100 行 |
| **PT-3** | 阶段同伦群同构 i≤n：πᵢᵈ(Xₙ) ≅ πᵢᵈ(X)（Ωⁿ 路线） | n=1/2 实例 | 50-80 行 |
| **PT-4** | Postnikov 不变量离散对应 kₙ（阶段粘合数据/扩张类） | S²ᵈ k₂ 实例 + K₃ 对账 | 60-100 行 |
| **PT-5** | T⁶/(Z/3Z)⁶ 有限实例化 + 塔终止性（有限生成 vs 无限同伦群分界） | T⁶ 实例+终止判据 | 40-80 行 |

**预算**：合计 250-350 行（任务书口径内）｜**执行**：探针先行（_PPT 系）→ 并入 PostnikovTruncation 或新件。

## 五、复用地图（本地优先）
`_PPI5` 系（Sⁿᵈ/DHomotopy/BMapQ/Chain/Ωⁿ）｜`_PPI5f`（Ω3Walk/fill-tri）｜`PostnikovTruncation`（disp 截断对账件）｜`ChainQuotIso`/`FreeAbQuotient`（商面）｜`MorseSqZeroK3`（对账数据）。

## 六、诚实边界
- PT 系列证完前全 pending（骨架非证明）；
- 「离散对应」措辞纪律：PT-2 的截断性质是**组合形**（walk/Ωⁿ 层），不是空间截断真身——头注照 PostnikovTruncation 诚实标注范式；
- E1/CRT 行列式分解**不在本线**（独立线性代数任务——审核裁定）。
