# Cook–Levin 路线提案

> **裁决性质**：**智能体提案**（2026-10-30），**待人类确认**。本文件不构成裁决。
> **效力**：若人类批准，则按本文件的里程碑执行；并按现行纪律同步更新
> `SATRed §6(i)`、`SATMember §6(iii)`、`SATFam §6` 的「W2 立界不排期」注记为「已排期（M1–M4）」。
> **前置事实**：`docs/PNP/Cook-Levin-资产普查-2026-10-30.md`（实测行数与缺口清单）。
>
> **执行状态（2026-10-30）**：人类已批准 **M1** 并开工；**M1 已完成**
> （`6884e65` CNF.agda 253 行 / `4f41962` CNF-Tseitin.agda 439 行 /
> `eccae49` 三处 W2 立界注记同步）。M2–M4 未开工。

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
| **M2** | `NPClass` 旁加 `InNP-TM`（`TM` + 步数界多项式 + 见证 = 输入/猜测的拼接）+ `InNP-TM ⟹ InNP`（验证器 = `runN` 的计账包装） | 250–400 | 同 M1；至少一个具体 TM 的实例（可直接用 `tm-head`/`tmc`） |
| **M3** | tableau 构造：变量编号 `(t,i) ↦ Fin`（`/`,`%` 引理）+ 六个子句族 + 初始/终止格局 | 700–1200 | 同 M1；size 界 `O(p²)` 显式陈述 |
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
