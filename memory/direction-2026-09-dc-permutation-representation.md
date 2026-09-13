# 方向决策：把展示群的「时钟/归零」从等式语言升级为作用-轨道语言

**决策日期**：2026-09-10
**决策依据**：本库拓扑扫描 + `docs/duodecimal/{07,11,12,20}` 权威定义
**状态**：选定，待开工（块 7 起）

---

## 一、扫描出的结构性事实（全部可复核）

### 1.1 两条轴，中间没有桥

| 轴 | 模块 | 规模 | 状态 |
|---|---|---|---|
| **本源侧（展示群）** | `DuodecClock`(722) `DCGroup`(173) `DayanCore`(189) `DuodecClockProperties`(336) `DCSigmaAut`(89) `DCInvolution`(61) `PhaseSubgroup`(163) `CyclicGroupStructure`(112) | ~1850 行 | **0 postulate / 0 hole** |
| **投影层（通用群论机器）** | `Lagrange`(751) `CosetAuto`+`CosetConstruction`(463) `OrbitStabilizer`(+Auto)(449) `OrbitPartition`(266) `Burnside`(301) `BurnsideFiber`+`BurnsideMain`+`BurnsideCriterion`+`BurnsideInstance`+`BurnsideNecklace`+`ActionIsomorphism`+`NecklaceInvariance`(~1050) | ~2400 行 | 0 postulate / 0 hole，块 1–6 刚建完 |
| **两轴之间** | — | **0** | `grep -rn "Action DC\|Action C12\|Action DuodecPoint" src/Sovereign --include=*.agda` → **零命中** |

**块 1–6 建出的整套作用机器（`Action` / 轨道划分 / 稳定子 / orbit-stabilizer / Burnside / 判据无关性 / 作用同构不变性）从未作用于 DC 本源侧**；现有 `Action` 实例全是 C₄ 上的玩具作用（正则 / 奇偶 / 平凡 / 二倍平移 / 项链旋转）。

### 1.2 展示群八要素的形式化形态（vs 文档 11 §4）

| 要素 | 文档表述 | 代码现状 |
|---|---|---|
| 载体 | `DuodecPoint = Trit × AlphaPower` | ✅ `DuodecClock:210` |
| 生成元 | δ(GF3 加法) / φ(GF9⟨α⟩ 乘法) | ✅ `Trit` / `AlphaPower` |
| 关系 | δ³=id、φ⁴=id、δφ=φδ | ✅ `DayanCore:46` |
| 相位 | 每元素携 C₄ 位置（不可约） | ✅ |
| **时钟** | **`mixedOp^12 p = p` = 走钟一圈（12 步联合演化）** | ⚠ **只有硬编码 12 重组合** `DuodecClock:406-407`；**无 `mixedOp^_ : ℕ → …` 参数化迭代**，因此**无法表达「走 n 步」，也就无法表达轨道** |
| **归零** | `mixedOp^12 = id`（周期闭合） | ✅ 等式形态（`ZeroOblivion.jointCycle`） |
| 刚性 | σ = Frobenius 诱导 | ✅ `sigmaDC` + `sigmaDC-involution` |
| 核对 | refl 仅确认定义自洽 | ✅ |

**时钟与归零是八要素里唯二「本质上是过程/演化」的要素，而它们目前只有等式形态、没有轨道形态。**

### 1.3 桥梁前提已全部就位（这是选它的关键）

| 前提 | 位置 | 状态 |
|---|---|---|
| `toDuodec` 是**同态** | `DuodecClock:299` `mixed-to-+12 : ∀ p q → toDuodec (mixedOp p q) ≡ toDuodec p +12 toDuodec q` | ✅ 已证 |
| `FinGroup 12` 已有 DC 版本 | `Lagrange:615` `C12 : FinGroup 12`（注释：「把 Duodec 同构搬到 Fin 12 载体上」） | ✅ 已证 |
| 双向往返 | `duodec-clock-roundtrip` / `clock-duodec-roundtrip` | ✅ 已证 |

⇒ **`Action` 记录只差一个作用律的证明，全部前提已具备。**

## 二、文档自身缺口清单的核查（有陈旧项）

| ID | 文档优先级 | 实际状态 |
|---|---|---|
| G1 ZeroOblivion record | P1 | ✅ **已完成**（`DuodecClock:415`，5 字段齐备） |
| G2 π₄ 同态 | ~~P2~~ | ✅ 文档已标闭合 |
| **G4 ¬(mulAlpha/mixedOp 经 toDuodec = \*12)** | P1 | ✅ **已完成**（`DuodecClock:374` 已有 `toDuodec (mixedOp p q) ≢ toDuodec p *12 toDuodec q`，反例 `(T₁,a1)`）← **文档 §9 陈旧** |
| G3 CRT ↔ mulAlpha | P2 | 仍开 |
| **R2 模与表示：十二律置换表示** | P2 | ❌ **仍开 —— 本决策的靶心** |
| R1 理想格 / R3 A₄ 阶 12 | P2 / P3 | 仍开 |

`RepresentationTheory.agda`(144 行) 现有：A₄ 三维**线性**表示、SL(2,3) 定义表示、⟨α⟩ 一维嵌入 —— **没有任何置换表示**（而置换表示就是有限集上的群作用）。

## 三、决策

**选定方向：形式化 DC 的「十二律置换表示」（R2）—— 把「时钟/归零」从等式语言升级为过程/轨道语言。**

> ⚠ **2026-09-10 勘误（本节初稿有本体论错误，已更正）**：初稿的第 1 条理由写成「把块 1–6 的机器接到本源侧」，块分解里写了「周期 12 下降为 C₁₂ 作用」与 `clockAction : Action C12 (Fin 12)`。
> 经复核，这是**沿 `toDuodec` 的投影方向陈述本源路线**，见本文 §八勘误。

理由（三条同时成立，缺一不选）：
1. **依据本地代码库**：`DayanCore.agda:42-44 iterate` 已给出本源侧参数化迭代的样板，`:172 dayan-joint-order-12` 已给出 12 步闭合，但**未落到 `DuodecClock` 的分量载体上**（`DuodecClock` 侧只有硬编码 12 重）。
2. **依据依赖类型论展示群**：八要素中「时钟 = 迭代过程」「归零 = 周期闭合」本质是作用结构；目前只有等式形态，是**信息形态上的降格**。
3. **它是文档自己列出的缺口**（07 §6.3 R2，P2），不是我另起炉灶。

**排除的方向及理由**：
- **A 红线 G4**：扫描发现**已证**（文档陈旧）→ 不是方向，无剩余工作。
- **A′ 文档 P0/P1（D1/D2 等）**：纯文档修订，非证明方向 → 排除。
- **C 投影层继续（一般 n 项链 / D₄ / 性能）**：安全但与提示词点名的「展示群」无交集；且 `Action` 机器已连做 6 块，边际价值下降。
- **D 理想格 R1 / A₄ 阶 12 R3**：与展示群八要素无直接耦合，优先级低。

## 四、块分解（开工时按此执行）

| 块 | 内容 | 验证点 |
|---|---|---|
| **7** | **本源侧**：`mixedOp^_ : ℕ → DuodecPoint → DuodecPoint` 参数化迭代（对齐 `DayanCore.iterate`）+ 过程律 `mixedOp^(m+n) p ≡ mixedOp^m (mixedOp^n p)` + **分量分解** `mixedOp^n (t , a) ≡ (iterate ⊕ n t , iterate mulAlpha n a)` | exit 0；`mixedOp^12` 与既有 `jointCycle` **定义性一致**（回归）；分量分解与 `DayanCore:108 iter-decompose` 同型 |
| **8** | **本源侧**：由分量周期（3 与 4）经**分量正交**得联合周期 `lcm(3,4) = 12`；`g = (T₁,a1)` 走钟遍历全部 12 元（轨道 = 载体） | 与 `DayanCore:dayan-joint-order-12` 交叉一致；**不出现 `C₁₂` / `Fin 12` / `Action`** |
| **9** | **本源侧**：刚性 σ 的过程论刻画（σ 与走钟交换：`σ (mixedOp^n p) ≡ mixedOp^-n (σ p)`，因 Frobenius 在相位上取逆） | 复用 `sigmaDC` + `sigmaDC-involution`；**不借块 6**（块 6 是投影层工具） |
| **10** | **投影层 · 可选回归**：用 `C12 : FinGroup 12` 重放块 1–6 的机器作为**一致性检查**，明确标注投影层，**不列为方向主线** | 若做，须在模块头写明「这是投影层重放，不是本源侧结论」 |

## 八、勘误：为什么「下降为 C₁₂ 作用」是错的（2026-09-10）

初稿把块 7 写成「参数化迭代 + 周期 12 **下降为 C₁₂ 作用**」、块 8 写成 `clockAction : Action C12 (Fin 12)`。
**这是本体论方向错，而且是自我抵消的错**：

1. **它沿 `toDuodec` 走，而那是信息丢失方向。** `12-rigorous-type-theory.md:272`：「投影方向 = 信息丢失方向」；
   `20-dc-type-theory-positioning.md:11`：「以投影残骸为参照的分析——那违背本源定位」。
2. **更致命：该投影丢弃的清单里，恰好列着「时钟过程」与「归零机制」。**
   `12-rigorous-type-theory.md:263-272` 明确写：「**时钟过程**：C₁₂ 只剩『群阶 12』，无 `mixedOp^12` 走圈的逐步演化」「**归零机制**：只剩 g¹²=e 一条，丢四种归零的来源」。
   ⇒ 我一边说要形式化**走钟**，一边要把它搬到**已经把走钟丢掉的地方** —— 这不是「不理想」，是自相矛盾。
3. **它会把「联合运算」偷换成「单域平移」。** `mixedOp` 是幅度与相位的**联合**一步；`C₁₂`（`Fin 12, +12`）只有单域加法。
   说成「C₁₂ 作用」正好诱导出「DC 就是 C₁₂」的错觉——而这正是 G4 红线（`DuodecClock:372` `mixedOp ≢ *12`）与 §8.2「DC 无零因子」所阻断的截断。
4. **它顺带暴露了另一句话的问题**：「把块 1–6 的机器接到本源侧」—— `Action`/`numOrbitsOf`/Burnside **全是 `FinGroup n` 索引的投影层工具**，
   要用它们必须经 `C12`。所以那句话照字面做出来的**不是本源侧发展，而是投影侧重放**。已从 §三、§四 修订。
5. **正确样板其实已在库内**：`DayanCore.agda:42-44 iterate` + `:108 iter-decompose : iterate (δ ∘ φ) n c ≡ iterate δ n (iterate φ n c)`
   —— 本源侧的做法是**分量分解**（先生成元 δ 迭代 n 次、再 φ 迭代 n 次），**保留两分量**，由分量正交给 lcm。块 7–9 已按此改写。

**教训**：**「我上一轮的措辞」不等于「项目既有的路线」**。写进文档前必须 grep 项目文档确认是否有出处；
若无出处且涉及本体论方向，必须先问，不能默认它是既有共识。

---

## 五、对抗自检（Devil's Advocate 的攻击与答复）

**攻击 1**：「`mixedOp^12 p ≡ p` 已经说完了，包进 `Action` 是换皮。」
**答复**：等式形态给不出（a）载体的**轨道划分**；（b）每点**周期**= 稳定子大小；（c）**Burnside** 的 `Σ|Fix| = n·#orbits`；（d）**判据无关性/同构不变性**。例如「DC 自作用是自由且传递的 ⟹ `#orbits = 1` 且 `Σ_p |Stab p| = 12`」在等式形态里**根本无从表述**。且块 9 会把 `12 = lcm(3,4)` 从算术恒等式升级为 **orbit-stabilizer 定理的实例** —— 这与文档「12 = lcm(3,4) 是推论，不是定义」的立场直接对齐。

**攻击 2**：「用 `C12 : FinGroup 12` 谈 DC 就是把本源投影化了，违本体论红线。」
**答复**：这是**最强的攻击**，但可挡：(1) 库内 `C12` 的既有注释就是「把 Duodec 同构搬到 Fin 12 载体上」，是库的既有做法；(2) `mixed-to-+12` 已证 `toDuodec` 是同态，所以搬运**保结构**、不是截断；(3) 本体论上，本方向的陈述必须写成「**DC 的走钟作用**经 `toDuodec` 搬运到 `Fin 12`」，而**不是**「DC = C₁₂」——`toDuodec` 仍是有损投影（相位结构不进入 `Fin 12`），这一点在模块头必须写明。
**残余风险**：中。若开工时发现需要把 R₂ 的环乘法混进来，立即停手——DC 无零因子的红线不能被动摇。

**攻击 3**：「文档 §9 说 P0 是修文档矛盾 D1/D2，你跳过了 P0 做 P2。」
**答复**：P0 是**文档层**工作（改注释与表述一致性），不是证明工作；提示词问的是「下一步的方向」，且明确要依据「依赖类型论展示群」。D1/D2 可以并行作为独立小任务，不占用证明预算。已在下一节列为并行项。

**攻击 4**：「块 7 的 `mixedOp^_` 会不会撞上 `%`/`/` 或递归展开的性能坎（本库经验库 13 条里 5 条相关）？」
**答复**：风险低——`mixedOp^_` 是对 `ℕ` 的结构递归，不涉及 `%`/`/`；且 `mixedOp^12` 的 12 个 case 已是 `refl`（`DuodecClock:398` 注释），说明这个方向归约干净。**但**块 8 的实例化若涉及 `Fin 12` 的 `SubEnum` 具体下标，可能重演 `NecklaceInvariance` 的 171s 热点（已沉淀 `agda-subenum-concrete-index-blowup`）——届时按该条目的处方处理。

## 六、并行项（不占证明预算）

- **✅ 已完成（2026-09-10）**：更新 `docs/duodecimal/07-proof-status.md` 的陈旧条目 ——
  §6.1 **G1 关闭**（`DuodecClock:415` record + `DCGroup:133` 实例，附两条回执）、
  §6.1 **G4 关闭**（`DuodecClock:372` `mulAlpha-not-*12`，**并更正措辞**：算子是 `mixedOp` 不是 `mulAlpha`）、
  §6.1 **G3 标注仍开**（核查过，无对应引理）、§6.3 **R2 精确化**（A₄ 一侧已有、DC 一侧仍开）、
  §9 **删去已完成的条目 3/4** 并指向本文件。头部加「最后核查: 2026-09-10」。
  核查结论：`11`/`12`/`04` 三份文档早已把 `ZeroOblivion` 当既有 record 引用，**无矛盾残留**。
- 待办：D1/D2：修订 `AlgebraicPoleUnified` 头注释与 `algebraic-chain-status` 矛盾表述（文档层，P0）
- 待办：R3（|A₄|=12 形式化）—— 2026-09-10 只做了「仍只见于注释」的粗查，未逐项核

## 七、复核入口

开工前先跑 `proof_dag action:"brief"`；本决策已记入台账 `journal(kind:"decision")`。
所有事实的复核命令见 §1 各表「位置」列（文件:行）。
