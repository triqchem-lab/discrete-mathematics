# D1/D3 研究报告（双章）

> 课题基线 v2｜P1 两件｜六节结构×2｜2026-10-11
> 方法：本地代码实测（bash 原生 grep——python-subprocess-grep 假阴性事故教训）+ 文献检索
> **纯研究零源码改动**；研究报告先行，实施决策独立

---

# 第一章 D1：分水岭定理的一般化（一般图 π₁ᵈ 成群判据）

## 一、数学对象

**问题**：分水岭定理已证 two-chain 特例（π₁ᵈ(Gcmp two-chain)=2 元幂等幺半群 ∧ π₁ᵈ(Gskel two-chain)≅(ℕ,+) ⇒ ¬MonoidIso）；**一般图** G 的 π₁ᵈ(G,x) 何时成群？

**特例的机制回顾**（本地实测）：
- `_PPI4b:13`：Gcmp 侧 **[e01,e10] ∼ [loop] 且全类幂等**——去而复返可并类；
- `_PPI4b:96-97`：无同构汇合——全类幂等传递（Gcmp 侧幂等 ⇒ 对侧幂等）vs Gskel 非幂等（[e01∷e10∷nil]⊞自身=[4 边]≠[2 边]）⇒ 矛盾；
- 根源 = **slide 并类性**：Gcmp 的去返对 (e01,e10) 在 AHomotopy（slide/expand）下可消，Gskel 的不可消（e01≠e10 独立构造子）。

## 二、经典路径

- **Babson-Barcelo-de Longueville-Laubenbacher "Homotopy theory of graphs"**（2006，[zbMath 1108.05030](https://zbmath.org/pdf/1108.05030.pdf#1#1)）：图同伦论的 C-cycle/A-homotopy 框架——q-loop 等价（(σ0,…,σn,σ0) 型循环消去）；
- **Barcelo-Laubenbacher "Perspectives on A-homotopy theory"**（[zbMath 02207449](https://zbmath.org/pdf/02207449.pdf#1#1)）：A-同伦的应用综述；
- **Smith 博士论文**（[GVSU](http://faculty.gvsu.edu/smithshe/files/MainDissertationFile.pdf#14#2)）：Laubenbacher 线图同伦综述——q-loop 等价 ([σ]=(σ0,…,σi,σi+1,…,σn,σ0) 的等价处理)；
- **经典判据的形状**：经典 A-理论在**对称图**（无向）上 q-loop 消去自动可用 → 群；**本框架** slide/expand 只消特定对——**对称 ≠ 可消**（Gcmp 对称仍幂等不成群的机制=slide 并类性是定义面性质非对称面性质）。

## 三、本地对接

| 件 | 锚点 | 作用 |
|---|---|---|
| 分水岭定理（two-chain） | `_PPI4b:13,96-97`（证明结构）+ 回执 `e3c0b2c0` | 判据的原型 |
| NoTriangle/AStep-sk-empty | `_PPI4h:33`（NoTriangle 定义）+ AStep-empty←/△-from-AStep 两方向 | 无三角图族=零腔图判据 |
| gskel-classify 双证 | `_PPI4g:149` + `_PPI4m:129`（classify-2） | Gskel 侧 (ℕ,+) 结构基准 |
| 端点泛化+UIP(V) 前提 | `_PPI4o:11`（核心发现注记）+ canonical/decomp-unique 全落地 | **泛形化的方法论基础** |
| excursion/cutZ/canonical | `_PPI4k`（构造携带 resZ）/`_PPI4l`（泵引理+uniq-w2w2） | 长度/分解机件=必要性方向的工具 |
| Graphs 面 8 件 | `Topology/Graphs/`（GraphBasic/Connectivity/Cycles…实测 8 模块在盘） | 一般图的承载 |
| CycleSpace 雏形 | `Cycles.agda:64`（record CycleSpace (G : Graph) : Set₁——群律立界） | 同调对接面 |
| Dec 面 | `Foundation/LogicDecidable`（回执 d683475） | 判定复杂度承载 |

**展示群八要素**：一般图判据的八要素 = 载体（Walk G x x 商）/生成元（边）/关系（AHomotopy 的 slide-expand 规则族——**判据=关系体系何时含逆元消去规则**）/时钟（walk 长度）/归零（可消性）/核对（two-chain 特例互证）——生成结构口径一致。

## 四、严格设计

**判据定义（候选）**：
```
Mergeable G := ∀ {u v} (e : edge G u v) → Σ (e' : edge G v u),
  AHomotopy 承载：cons e (cons e' (nil u)) ∼ᴬ nil u     —— 去返可消
```
（注：Gcmp two-chain 实测满足——`_PPI4b:13` 的 [e01,e10]∼[loop]；**关键=可消性是 AHomotopy 定理级性质**，非边的对称性本身——Gcmp 对称而可消的机制在 slide 定义对可比对的归约形）。

**定理骨架（双向）**：
- **方向一（充分）**：Mergeable G ⟹ π₁ᵈ(G,x) 成群——逆=[w]⁻¹=[reverse w]；证明路线=slide 消去对 walk 结构归纳（端点泛化机件 `_PPI4o` 承载——loop 型永不拆分）；
- **方向二（必要，反向否决）**：¬Mergeable（存在边 e 无可消返对）⟹ ¬群——路线=该边的幂行走类长度计数单射（npos 计数机件 `_PPI4i`+resZ `_PPI4k`——**泛形需 UIP(V) 前提或构造携带重写**（`_PPI4o` 已证 UIP 前提形可行——方法论就绪））；
- **算法骨架**：Mergeable 判定 = 每边查返边+消性（消性判定需 AHomotopy 等价的可判定性——Dec 面衔接；子问题：AHomotopy 可判定性=独立研究面）；
- **分类二分**：成群 ⟺ Mergeable（UIP 前提下）——全图二分定理骨架。

**与同调的关系**：π₁ᵈ 的交换化 ↪ H₁（圈空间）——Gskel 案：h₁ = rounds 计数（`_PDH1:9`：H₁^FAb(Gskel two-chain)≅(ℕ,+) 对角生成——**h₁ 恰是 π₁ᵈ→交换化的实现**）；一般图的 h₁ 立界于 `_PDH4/_PDH5` 的泛型面。

## 五、诚实边界

| 类 | 内容 |
|---|---|
| **可证（就绪）** | 方向一构造性（slide 归纳——机件全在）；two-chain 特例全证（原型）；Gskel 长度计数面（npos/canonical） |
| **不可证-现状** | 方向二一般形的必要性：**UIP(V) 前提**（`_PPI4o:11`——无 UIP 的 HIT 顶点型情形立界原句）或构造携带重写（~150-250 行——`_PPI4n` 路线实测） |
| **需新工具** | AHomotopy 可判定性（算法面的前置）；一般图的 2-环消性与 slide 定义的全分类（slide 规则族的一般枚举） |

## 六、依赖与优先
- 前置：分水岭定理✅/canonical✅/端点泛化✅/Dec✅——全齐；
- 后续：**A2**（修正案 A=backtrack 入定义 ⟹ Mergeable 面 rewrite——分水岭 v2 的生成方式重述）；实施候选批 **D1-impl**（~100-150 行：Mergeable 定义+方向一构造性+方向二 UIP 前提形+two-chain 互证）；
- 开放问题：①可消性判据的**完整**刻画（slide 族一般枚举）②复杂度常数面③与经典 A-理论的 q-loop 消去的精确定理级对应。

---

# 第二章 D3：Dodziuk 逼近→替代的严格论证

## 一、数学对象

**问题**：Dodziuk (1976) 证明**组合 Hodge 收敛到连续 Hodge**（逼近）；本地框架主张「离散 Hodge 可替代连续 Hodge」——该主张的严格数学论证是什么？（任务书 4.3 诚实界原文：「逼近≠替代——框架主张需独立论证」）。

## 二、经典路径（文献实测）

- **Dodziuk 1976**（de Rham-Hodge 收敛；[作者文献页 QC CUNY](http://qcpages.qc.cuny.edu/~jdodziuk/biblio.pdf#1#1)）：单纯复形上组合 Hodge → 流形 Hodge 的**收敛定理**（带网格参数 ε→0）；
- **Whitney/de Rham 映射线**（[ICM 1974 卷](https://media-platform.mathunion.org/fileadmin/ICM/Proceedings/ICM1974.2/ICM1974.2.ocr.pdf#15#11)：W_n/R_n 映射+内积——逼近论的工具层）；
- **有限元 Hodge 收敛**（[Wardetzky Thm 3.4.2 Whitney-approximation of Hodge decomposition](https://refubium.fu-berlin.de/bitstream/handle/fub188/3519/3_Wardetzky_ch3.pdf?sequence=4&isAllowed=y#10#8)）：Whitney 逼近定理——现代有限元形态；
- **组合余微分一致性**（[AMS 2014](https://www.ams.org/journals/) 面——combinatorial codifferential 的分析对应操作）。

**定性**：经典路径全部是**逼近/收敛型**定理——依赖**实数/网格极限/ε-δ**（连续统结构）。本地红线（禁 Float/禁连续统对象层）⇒ 逼近定理本身**不可本地形式化**（元层引用可以，对象层不行）。

## 三、本地对接

| 件 | 锚点 | 状态 |
|---|---|---|
| EckmannGF3 | `Application/EckmannGF3.agda`（在盘实测） | GF(3) Hodge 分解面（子空间和） |
| EckmannNonSplitting | `Application/EckmannNonSplitting`（ones-in-im∂₂ = sym face-cycle——im∂₂ ∋ oneV 非零见证） | **不分裂已证** |
| DiscreteMorseTheory/General | `Application/`（morse-ineq₀/₁/₂/criticalComplex——实测锚） | 临界计数面 |
| FreeAb 族 | `Application/FreeAb*`（多件实测在盘） | 同调承载 |
| **DiscreteHodgeDecomposition** | **不在盘**（ls 实测——Dodziuk 形式化批未落/未报，另账） | **如实注：逼近定理的离散面未建** |
| 任务书 4.3 | 诚实界原文（逼近≠替代） | 主张的边界声明 |

## 四、严格设计

**①「替代」三义的精确化与判定**：
| 义 | 定义 | 本地可证性 |
|---|---|---|
| (a) **等价** | 连续↔离散 Hodge 理论范畴等价 | ❌ 需连续侧形式化（违宪）——**否决** |
| (b) **逼近** | 收敛定理（Dodziuk 原义） | ❌ 需实数/极限（违宪）——外部定理引用面 |
| (c) **自足+对应** | 离散 Hodge **独立自洽**建立 + 与连续的关系=外部对应定理（桥） | ✅ **可行且大体已实现** |

**②离散自足性论证路线（主设计）**：Eckmann 线**已自足**——GF(3) 上的 ∂/δ/内积/调和面全构造性（0-postulate），分解定理（子空间和形）+不分裂定理已证——离散 Hodge 作为**独立数学理论**的成立性不依赖任何连续内容。论证形式：A1 同款「本体论独立性」论证（组合本源 vs 经典拷贝）。

**③Eckmann 不分裂的定位（关键澄清）**：不分裂定理**不是**「替代」的支持或反对——它是**离散基座上内积非正定的数学现象**（独立定理）。它对主张的真实作用：证明**离散理论有自己的现象学**（连续 Hodge 无此现象）——支持「离散=独立研究对象」的定位，而非「离散=连续的替身」。

**④主张修正候选（本报告核心结论）**：
> 原主张「离散 Hodge 可替代连续 Hodge」**降格并精确化为**：
> **「离散 Hodge 理论在有限域基座上自足且已形式化（Eckmann 面 A 级）；与连续 Hodge 的关系=外部对应定理（Dodziuk 收敛=引用面，不形式化）」**
> ——即主张从「替代」（等价性声称）修正为「自足+引用」（独立性声称+桥接面）。

## 五、诚实边界

| 类 | 内容 |
|---|---|
| **可证（已就绪）** | 自足性论证（Eckmann 线 A 级已证面+FreeAb 承载）；现象学独立性（不分裂定理） |
| **不可证** | 等价义/逼近义的定理形式化（连续统红线——**结构性不可证**非工程难） |
| **需新工具** | 无（修正后的主张不再需要新工具——收敛面走外部引用） |
| **另账** | Dodziuk 逼近定理的**离散面形式化**（DiscreteHodgeDecomposition——未落盘，Dodziuk+Plato 批在途未报）：即使落地也只是「逼近的组合骨架」，不改变本报告的定位结论 |

## 六、依赖与优先
- 前置：Eckmann✅/FreeAb✅/任务书 4.3✅——全齐；
- 后续：主张修正=**人类裁决面**（建议 journal decision open：「替代→自足+引用」的措辞变更）；Dodziuk 形式化批（69acb012 未报——存疑核查）；Wardetzky 线（有限元收敛——外部引用面不动）。

---

## 附：锚点核实记录（2026-10-11 实测——零降档）
| # | 锚 | 实测 | 判 |
|---|---|---|---|
| 1 | 分水岭证明结构 | `_PPI4b:13`（[e01,e10]∼[loop] 幂等）+`:96-97`（无同构汇合/矛盾形） | ✓ |
| 2 | NoTriangle/AStep-sk-empty | `_PPI4h:33`+两方向件 | ✓ |
| 3 | gskel-classify 双证 | `_PPI4g:149`+`_PPI4m:129` | ✓ |
| 4 | UIP(V) 前提/端点泛化 | `_PPI4o:11`+decomp-unique 落地 | ✓ |
| 5 | Graphs 面 8 模块 | `Topology/Graphs/` ls 实测 | ✓ |
| 6 | CycleSpace record | `Cycles:64`（Set₁+群律立界） | ✓ |
| 7 | Eckmann 两件 | `Application/{EckmannGF3,EckmannNonSplitting}` 在盘 | ✓ |
| 8 | DiscreteMorse 泛型件 | `DiscreteMorseGeneral:52-57`+`DiscreteMorseTheory:23/43` | ✓ |
| 9 | h₁=rounds（H₁≅(ℕ,+)） | `_PDH1:9` | ✓ |
| 10 | **DiscreteHodgeDecomposition 不在盘** | ls 实测 No such file | ✓ 如实（Dodziuk 批未落另账） |
| 11 | AtkinQ1（Q-analysis q=1） | `Topology/AtkinQ1:4-6` | ✓ |

**文献出处**：[Babson-Barcelo-de Longueville-Laubenbacher 2006](https://zbmath.org/pdf/1108.05030.pdf#1#1)｜[Barcelo-Laubenbacher Perspectives](https://zbmath.org/pdf/02207449.pdf#1#1)｜[Smith 论文综述](http://faculty.gvsu.edu/smithshe/files/MainDissertationFile.pdf#14#2)｜[Dodziuk 文献页](http://qcpages.qc.cuny.edu/~jdodziuk/biblio.pdf#1#1)｜[ICM 1974 Whitney/de Rham 面](https://media-platform.mathunion.org/fileadmin/ICM/Proceedings/ICM1974.2/ICM1974.2.ocr.pdf#15#11)｜[Wardetzky Whitney-approximation](https://refubium.fu-berlin.de/bitstream/handle/fub188/3519/3_Wardetzky_ch3.pdf?sequence=4&isAllowed=y#10#8)
