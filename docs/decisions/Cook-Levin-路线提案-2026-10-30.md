# Cook–Levin 路线提案

> **裁决性质**：**智能体提案**（2026-10-30），**待人类确认**。本文件不构成裁决。
> **效力**：若人类批准，则按本文件的里程碑执行；并按现行纪律同步更新
> `SATRed §6(i)`、`SATMember §6(iii)`、`SATFam §6` 的「W2 立界不排期」注记为「已排期（M1–M4）」。
> **前置事实**：`docs/PNP/Cook-Levin-资产普查-2026-10-30.md`（实测行数与缺口清单）。
>
> **执行状态（2026-10-30）**：人类已批准并开工；**M1、M2 已完成**。
> · M1：`6884e65` CNF.agda 253 行 / `4f41962` CNF-Tseitin.agda 439 行 /
>   `eccae49` 三处 W2 立界注记同步；
> · M2：`1945cdc` NPClass-TM.agda 260 行（`InNP-TM` + `InNP-TM→InNP` + 实例
>   `head-NP-TM`，0 postulate、5 条 refl 核对）。
> M3–M4 未开工。

## 一、提案

**路线 A：机器版 NP（`InNP-TM`）+ Cook–Levin tableau**，分四级里程碑，**先做公共前置 M1**。
路线 B（Fagin/ESO）降为备选；路线 C（只做 3CNF 化）被 M1 吸收。

## 二、依据（三条，全部来自普查实测）

### 2.1 库内三件前置全缺，且**成本集中在前置而非数学硬核**

- `Clause m = Lit m × Lit m × Lit m`（`SATMember.agda:62`）⟹ 只有 3-CNF；tableau 的
  「至少一个符号」「至少一个状态」「转移一致性」三族子句长度 4–7，**表达不出来**；
- `Formula m c = Vec (Clause m) c`（`:66`）且库内**零**「按需求构造公式」先例
  （唯一来源是 `decFormula` 从固定布局解码，`:170`）；
- `InNP.np-verifier` 是任意总函数（`NPClass.agda:48`），无转移表 ⟹ 无「第 t 步第 i 格」可读。

### 2.2 三条缺口里，只有一条是真的深件

| 缺口 | 性质 |
|---|---|
| 一般 CNF + 可构造公式（§3.1/3.2） | **工程**（+ `Vec` 长度算术，可用 `List` 绕开） |
| 机器版 NP（§3.3） | **工程**：`TM` 是 record、`runN` 是构造性函数 ⟹ 「跑 p n 步」可直接定义成 `Counted Bool`。**注意方向**：`InNP-TM ⟹ InNP` 可做；`InNP ⟹ InNP-TM` 才是 Church–Turing 深件，本提案不碰 |
| 满足赋值 ⟹ 运行存在（§3.5） | **数学**（CL 的实质），估 300–500 行 |

### 2.3 为什么不选 Fagin 作首选

`FMTK`（226）+ `FMTK-ESO`（280）+ `FiniteModelTheory`（145）只提供**语义层**
（公式类型、`Env`、`evalFlat`/`evalExt`、`Sat`），**归译为零**：
既没有 `NP ⟹ ESO`，也没有 `ESO ⟹ SAT`。而 Fagin 本体（NP = ESO）是 W2 的核心深件
（`FMTK-ESO.agda:16`、`:271` 已立界）。走 B 等于先证一个更深的东西再回到 SAT。

## 三、里程碑

| 级 | 内容 | 估（行） | 交付判据 |
|---|---|---|---|
| **M1（公共前置）✅ 完成** | `Complexity/CNF.agda`（253 行）：`Clause' = List (Lit m)`、`Formula' = List (Clause')`、`satClause'`/`satFormula'` + 计账版 + 拼接三条 + 3-CNF 嵌入 `formulaOf3` 与保真 `formulaOf3-sat`；`CNF-Tseitin.agda`（439 行）：`tseitin-split` + 等可满足**双向**（`tseitin-split-sound` / `-complete` / `-sat-elim` / `-sat-intro` / `-unsat`）+ 计数上界 | 350–500 | ✅ `EXIT=0`、0 postulate/hole、16 条 `refl` 核对、3-CNF 逐点一致（`formulaOf3-sat`） |
| **M2 ✅ 完成** | `Complexity/NPClass-TM.agda`（260 行）：`record InNP-TM`（转移表 + `tm-acc` 接受判据 + 冻结前提 `acc⟹halt` + 多项式界 + 猜测界 + 完备/正确）+ `NPT-run` / `NPT-verdict` / `NPT-verifier`（值/账两条精确等式）+ `InNP-TM→InNP` + 实例 `head-NP-TM : InNP-TM L-Head₁` | 250–400 | ✅ `EXIT=0`、0 postulate、5 条 refl 核对（p=1 / wLen=0 / 三条输入上的验证器值） |
| **M3（M3a ✅ / M3b ✅ / M3c 进行中：G1 ✅ G2 ✅）** | M3a ✅ `Tableau.agda`（291 行）：抽象原子 CNF + `oneHot`/`oneHot-sat` + 搬运 `AtoCNF-sat`（**只需一个函数** `e : A → Fin (suc m)`）；M3b ✅ `Tableau-Tape.agda`（226 行）：**相对头偏移视图** `tH`/`tL k`/`tR k` + 三条一步窗口事实（右移 / 左移·左空 / 左移·左非空）+ 初值视图 | 700–1200 | M3a/M3b：✅ `EXIT=0`、0 postulate、各 5 条 refl 核对。M3c 走 **(B) 相对行**，按 `docs/plans/m3c-atomic-plan.md` 分七闸门推进：**G1 编号层 ✅**（`Tableau-Tape.agda` 660 行，A1–A8 齐）；**G2 池 ✅**（`Tableau-Pool.agda` 207 行：`poolSize = suc T · ((3·L) · V)`、`poolEnc`/`poolDec`、`poolDec-enc` 往返、`poolLit` 接 `CNF.Lit`；stdlib `remQuot-combine`，零除法）；**G3 六族子句 ✅**（`Tableau-Clauses.agda` 447 行：C1 符号 oneHot、C2 `(q,p)` oneHot、C4 转移三支、C5 平移、C6 初始/终止、C7 `tableauOf`；含 `succRow` 后继行索引与 `InOff-shift*-fin`）；G4 方向一 → G5 方向二 → G6 3-CNF → G7 归约 待做 |
| **M4** | 提取引理（满足 ⟹ 运行存在）+ 组装 `∀L ∈ InNP-TM, L ≤ₚ SAT-3` + 与 `SATRed.Reduces` 对接 | 400–700 | 同 M1；`Reduces` 实例（非单点，参数化于池） |

M1 与 M2–M4 **解耦**：M1 不触碰 `InNP`，可独立交付；若 M1 后中止，仍是净收益。

## 四、M1 的具体设计（若要开工，就按这个做）

```agda
-- 一般 CNF：用 List 而非 Vec —— 整个绕开长度算术
Clause' : ℕ → Set
Clause' m = List (Lit m)

Formula' : ℕ → Set
Formula' m = List (Clause' m)

satClause' : ∀ {m} → Asg m → Clause' m → Bool      -- 空子句 = false（空析取）
satFormula' : ∀ {m} → Asg m → Formula' m → Bool     -- 空公式 = true（空合取）
```

三条必须证的语义事实：
1. `satFormula' a (map (clauseOf3) φ) ≡ satFormula a φ`（3-CNF 嵌入保真；`clauseOf3 l₁ l₂ l₃ = l₁ ∷ l₂ ∷ l₃ ∷ []`）；
2. 空子句/空公式的边界口径（`false`/`true`）与 `orC`/`andC` 的账目一致；
3. Tseitin：`satClause' a (l₁ ∷ l₂ ∷ … ∷ [])` 与「长度为 n 的子句 ⟹ n−2 个辅助变量」的等可满足双向。

**反例自检（已考虑）**：能否不做 Tseitin，靠「换布局让子句恒 3 长」？
**不能**——「每格至少一个符号」在 `|Γ| = 4` 时是 4 个正文字，任何定长 3 子句都无法等价表达
（满足该子句至少需要一个真文字，而 3 子句只覆盖 3 个候选）；必须辅助变量。故 Tseitin 必需。

## 五、保留的立界（不因本提案而变）

1. `InNP ⟹ 机器版`（任意总函数 ⟹ TM 转移表）= Church–Turing 深件，**不做**；
2. 通用机 / 停机不可判定（`TuringMachine.agda:16`）；
3. P ≠ NP 或任何分离断言（`NPClass` 头注纪律）；
4. 「直吃 `decLit` stride-3 重叠格」的布局桥（`SATLook §6(iii)`）——仍为可选省步，不排期；
5. `SATLook` 的停驻定理（一般性）——判决不依赖，不排期。

## 六、风险与退路

| 风险 | 退路 |
|---|---|
| M2 里 `runN` 对泛型 `halt` 不透明（`TMBridge` 头注已证） | 用 `MultiTape.runN2-blind` 或 SATLook 的相分离（`runB` 盲跑 + 泛型加法），已备范式 |
| M3 的 `Fin` 编号算术失控 | 变量改为 `Vec Trit W` 的「一维展开」而非 `Fin`（代价：内存 O(W) 而非 O(1)），或先把编号表物化为 `Vec (Fin W) W` 再查 |
| M4 提取归纳卡住 | 先把「每格恰一符号」单独立为引理（成对至多 + 至少一个），再装配；必要时先把 tableau 限定为**定长时间上界**（T 为参数而非多项式） |
| 规模超预算 | M1 之后按实测再裁 M3/M4 的子句族（可先做「转移一致性 + 初始/终止」而暂缓「至少一个状态」） |

## 七、需要人类确认的一件事

**是否批准把 W2 从「立界不排期」改为「排期（M1–M4）」，并先开工 M1？**

- 批准 M1：只动 `Complexity/CNF.agda` + `CNF-Tseitin.agda`（新文件），不改任何既有模块，
  风险最低、可独立回滚；同时补掉 `PropositionalLogic` 立界 (iv)。
- 只批准到 M1：M2–M4 维持立界，本文件降级为「前置已就位」的证据。

## 七·补 M3c 设计（2026-10-30，供下一段开工；**尚未写码**）

M3a/M3b 已交付（`Tableau.agda` / `Tableau-Tape.agda`，均 `EXIT=0`、0 postulate）。
M3c 剩四件，其中第一件是**未定的设计分叉**，必须先裁决：

### 分叉：绝对格号 vs 相对行

| 路线 | 形状 | 代价 |
|---|---|---|
| **(A) 绝对格号**（教科书式） | 原子 `(t, i, ·)`，`i < W = len + 2T + 2`，头起始于格 `T+1`；两侧 padding 用**单元子句**钉成空白 | 需要「头始终落在 `[1, W−2]`」的**区间不变量**（对 t 归纳，`ℕ` 区间算术）；M3b 的相对事实要先加一层「绝对 = 头位置 + 偏移」换算（含 `left` 逆序翻转） |
| **(B) 相对行**（M3b 的自然延续） | 行按**相对头的偏移**索引：原子 `(t, o, ·)`，`o` 覆盖 `[−T, len−1+T]`（**不对称**：头起于输入首格 ⟹ 输入整条在头右侧；错的写法是 `2T+3` 对称居中） | **不需要**坐标换算、不需要区间不变量；但每步要把偏移平移 ±1（左移入空白时为恒等）⟹ `TOff` 上的 code/decode + 界内保持——比 (A) 的区间算术轻 |

**建议 (B)**：M3b 已经证明「视角」应该是相对头；选 (B) 后 M3b 的三条 `tstep-*` **逐字**就是转移子句的语义，
而 (A) 要把它们翻译成绝对坐标（多一层引理，且仍要付区间不变量）。
选 (B) 的唯一新义务：偏移平移的 `Fin` 引理（估计 60–100 行）。

### 若走 (B)：子句族与提取链（可直接照做）

原子三族（`P = 2T+3`，`o` 以 `T+1` 为中心）：
- `Sym(t,o,a)`：第 t 行偏移 o 处的符号；`Head(t,o)`：头在该偏移；`St(t,q)`：状态。

六族子句（`→` 为蕴含子句，长度即为字面数）：
1. 符号 oneHot（每 `(t,o)`）：`⋁_a Sym` = `|A|` 字面 + 成对 2 字面 —— **直接套 M3a 的 `oneHot`**；
2. 状态 oneHot（每 t）：`|Q|` + 成对；
3. 头 oneHot（每 t）：`P` + 成对；
4. 转移（每 `(t,o,q,a)`，`δ(q,a) = (q′,a′,d)`）：`¬Head(t,o) ∨ ¬St(t,q) ∨ ¬Sym(t,o,a) ∨ Head(t+1,o+d) ∨ St(t+1,q′) ∨ Sym(t+1,o,a′)`（6 字面，d 三支各一族）；
5. 非头符号不变（每 `(t,o,a)`）：`¬Sym(t,o,a) ∨ Sym(t+1,o,a) ∨ Head(t,−1) ∨ Head(t,o) ∨ Head(t,+1)`（5 字面；偏移居中故 ±1 恒在域内 ⟹ **无边界案**——这是 (B) 相对 (A) 的主要省项）；
6. 初始（t=0）+ 终止（t=T 且 `acc` 态）：单元/短句。

提取链（赋值 ⟹ 运行），每步都用现成件：
- `oneHot-sat`（M3a）逐 `(t,o)` 取符号、逐 t 取状态与头位置 ⟹ 得 `c_t` 的三部分；
- 族 6 ⟹ `c_0 = NPT-initCfg`；
- 族 4/5 + **`tstep-R`/`tstep-L-nil`/`tstep-L-cons`（M3b）** ⟹ `c_{t+1} = step M blk c_t`（按 `d` 三支）；
- 族 6 的终止 + `tm-acc-halt`（M2 的冻结前提）⟹ 接受。
反向（运行 ⟹ 赋值）：给定 t 起跑，**按 M3b 的相对视图定义赋值**（`tSym`），每格恰一值取 T₁、同族其余取 **T₂**（M3a 头注的三值口径），六族逐族 refl/一步引理。

### 编号与 3-CNF（最后一步）

- `InNP-TM-fin`：给 `InNP-TM` 加 `Fin` 形态的状态/符号枚举（新 record，不动 M2）；
- `e : (Fin (suc T) × Fin P × (Fin |A| ⊎ Fin |Q| ⊎ Fin 2)) → Fin (suc m)`：**唯一一处算术**
  （只需 `e` 落在 `Fin` 内；`AtoCNF-sat` 已证不需要单射）；
- 长子句（族 1/2/3/4/5）经 M1 的 `tseitin-split` 落 3-CNF，辅助变元的新鲜/互异由同一编号给出。

