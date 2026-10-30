# Cook–Levin 资产普查（2026-10-30）

> **口径**：行数= `wc -l`（单文件，UTF-8 行数）；范围 = `src/Sovereign`（不含 `_build/`、`archive/`）；
> 事实以仓库当前 HEAD 为准（`git log -1` = `5b87180`）。本文件只记录**实测**，不记录估计；估计值一律标注「估」。

---

## 一、结论先行

**库里没有 Cook–Levin 需要的三件东西中任何一件**：

| 需要的东西 | 库内状态 | 证据 |
|---|---|---|
| **一般 CNF**（子句长度可变） | **没有**。`Clause m = Lit m × Lit m × Lit m`，**只有 3-CNF** | `SATMember.agda:62` |
| **按需求构造公式**（`Formula` 可拼接） | **没有先例**。`Formula m c = Vec (Clause m) c` 是长度索引；库内唯一的「公式」来源是**解码**（`decFormula`，固定 stride） | `SATMember.agda:66`、`:170` |
| **机器级 NP 定义**（转移表 + 步数界） | **没有**。`InNP.np-verifier` 是**任意 Agda 总函数**，无转移表 | `NPClass.agda:48` |

**2026-10-30 更新**：第 1、2 两件缺口**已由 M1 补上**（`CNF.agda` + `CNF-Tseitin.agda`，
见 §六 与 `docs/decisions/Cook-Levin-路线提案-2026-10-30.md`）；第 3 件（机器级 NP）
留待 M2。下表为普查当时（HEAD `5b87180`）的实测快照，保留以便对照。

⟹ Cook–Levin 在库内的成本**几乎全部落在「三件缺失的前置」**上，而不在 tableau 的数学硬核上。
这是本次普查最重要的结论：**先补前置，再谈 tableau；否则会在 `Vec` 长度算术与 3-CNF 表达力上撞墙。**

---

## 二、可复用资产（实测行数）

### 2.1 计账与类定义层（可直接用，零改动）

| 模块 | 行 | 提供 | CL 里的用法 | 复用度 |
|---|---|---|---|---|
| `Complexity/TimeBound.agda` | 204 | `Counted`/`value`/`steps`/`Mono`/`Pos`/`orC`/`andC`/`mono-*ˡ`/`le-mul` | 验证器计账、代价界装配 | 全量 |
| `Complexity/PClass.agda` | 160 | `TritLang`/`Decider`/`InP`/`head-P`/`inP⇒inNP` | `TritLang` 是两类共用的语言类型 | 全量 |
| `Complexity/NPClass.agda` | 138 | `record InNP`（8 字段）+ `P⊆NP` | **要扩展的点**（见 §3.3） | 结构复用、需加机器版 |

### 2.2 SAT 侧（语义 + 归约框架可直接用，CNF 结构不可用）

| 模块 | 行 | 提供 | CL 里的用法 | 复用度 |
|---|---|---|---|---|
| `Complexity/SATMember.agda` | 295 | `Lit`/`Clause`/`Formula`/`Asg`/`isT₁`/`evalLit`/`satClause`/`satFormula`/`satClauseC`/`satFormulaC`/`steps-satFormulaC`/`decFormula` | 语义与计账口径；**`Clause` 必须泛化** | 语义全量、结构需改 |
| `Complexity/SATFam.agda` | 539 | `SF-LSAT-fam` + `SF-fam-in-NP`（族在 NP）+ `SF-wlog3` 宽度簿记 | 目标语言的 NP 侧（CL 的归约终点） | 全量 |
| `Complexity/SATRed.agda` | 371 | `Reduces`（含 `r-mono-out`）/`red-refl`/`red-trans`/**`red-preserves-NP`** | CL 的**陈述形**直接复用：只差把 `r-map` 的构造填上 | 框架全量、实例待建 |
| `Complexity/SATMBridge.agda` | 380 | `SVM-cell`/`SVM-account`（3 步/子句）/双向语义桥 | 目标端（3-CNF）与机器的账目口径 | 参考 |

### 2.3 机器侧（模型可用，通用机没有）

| 模块 | 行 | 提供 | CL 里的用法 | 复用度 |
|---|---|---|---|---|
| `Automata/TuringMachine.agda` | 155 | `TM` record（δ/q₀/halt）、`runN`、`hdOf`/`tlOf`/`moveH`、`step` | tableau 要编码的**被模拟机器** | 全量 |
| `Automata/MultiTape.agda` | 198 | `TM2`/`C2`/`stepTape`/`runB`/`runB-+`/`runN2-blind` | 若被模拟机器是多带，用这套 | 需要时 |
| `Complexity/SATLook.agda` | 1690 | 2 带寻址机 + 语义桥 + 编码器 + `3c·(2m+7)` 精确账目 | **不降低 CL 成本**（见 §4.1）；只提供「相分离 / `runB-+` / 尾累积」三条工程范式 | 范式级 |
| `Complexity/TMBridge.agda` | 255 | 单旗舰 1 步桥 `TMH-head-bridge` | 「Counted ⇄ TM」的**实例级**做法 | 范式级 |
| `Complexity/TMBridge2.agda` | 286 | 2 步 + `Dir=L` 首实例、独立空白符字母表 `TMC-Σ` | 同上；`Σ` 与空白符冲突的处理先例 | 范式级 |

### 2.4 Fagin 侧（只是语义层，不是 Fagin 定理）

| 模块 | 行 | 提供 | 状态 |
|---|---|---|---|
| `Foundation/FMTK.agda` | 226 | `FTK-Formula k`（`Var = Fin k`）、`≤2` 元关系词汇、逐变元 ∃-over-`Fin n` 语义 | 就位 |
| `Foundation/FMTK-ESO.agda` | 280 | `FTK-ESO-Formula`/`Env`/`evalFlat`/`evalExt`/`Sat`/`tables`（ESO 语义 + 展平） | 就位；**归译缺失** |
| `Foundation/FiniteModelTheory.agda` | 145 | 双变元 FO + `evalF` + `Structure` | 就位 |
| `Foundation/PropositionalLogic.agda` | 136 | 命题语法 + `evalF` | 立界 (iv)：「CNF/范式转换（等值变形链）」**未做** |

---

## 三、缺口（精确到 file:line）

### 3.1 只有 3-CNF —— `SATMember.agda:62`

```agda
Clause : ℕ → Set
Clause m = Lit m × Lit m × Lit m
```

tableau 产生的子句族与 3-CNF 的适配情况（`Γ` = 带字母表，`Q` = 状态集）：

| 子句族 | 长度 | 3-CNF 友好？ |
|---|---|---|
| 每格至少一个符号 | \|Γ\|（常用 4） | **否** |
| 每格至多一个符号 | 2（成对） | 是 |
| 每刻至少一个状态 | \|Q\| | **否** |
| 每刻至多一个状态 | 2（成对） | 是 |
| 转移局部一致性 | 5–7 | **否** |
| 初始/终止格局 | 1–2 | 是 |

⟹ 一半子句族超长 ⟹ 必须 **3CNF 化（Tseitin/辅助变量）**，而这本身需要「新变元号分配」，即算术。

### 3.2 公式是长度索引的 `Vec` —— `SATMember.agda:66`

```agda
Formula : ℕ → ℕ → Set
Formula m c = Vec (Clause m) c
```

- 拼接 `Vec _ a` 与 `Vec _ b` 得 `Vec _ (a + b)` ⟹ 构造 O(p²) 个子句要携带一路 `+-assoc`/`+-comm`；
- 库内**没有**任何「按需求拼公式」的先例：全库返回 `Formula m c` 的函数只有两个，
  且第二个是第一个的直接包装 ——
  `decFormula : (m n) → Vec Trit n → Formula m (n / clauseW m)`（`SATMember.agda:170`）与
  `SF-decFormula-fam n x = decFormula (SF-wlog3 n) n x`（`SATFam.agda:489-491`，`SF-fam-dec-agrees` 明写「逐字同一项」）。
  两者都是**从固定布局的串解码**，不是构造；
- `SATFam` 的「族」也不是构造出来的：`SF-LSAT-fam n x = L-SAT (SF-wlog3 n) n x`（`SATFam.agda:443`）——是**谓词**，不是拼出来的 `Formula`。

### 3.3 `InNP` 的验证器是不透明函数 —— `NPClass.agda:48`

```agda
np-verifier : (n : ℕ) → Vec Trit n → Vec Trit (np-witLen n) → Counted Bool
```

任意 Agda 总函数没有转移表 ⟹ 无法从它读出「第 t 步第 i 格是什么」⟹ tableau 无从下手。
这正是 `SATRed.agda:8-11` 与 `:354-359` 已经写明的立界理由。

**但有一处可以精确利用**：反方向（机器是**数据** ⟹ 定义验证器为「跑 p n 步」）**不需要** Church–Turing，
因为 `TM` 是 record、`runN` 是构造性函数。所以 `InNP-TM ⟹ InNP` 是**可做的**，
而 `InNP ⟹ InNP-TM`（任意函数 ⟹ 机器）才是深件（`TMBridge.agda` 头注 / `PClass §6(i)` 已立界）。

### 3.4 变元编号要算术

`Lit m = Sign × Fin (suc m)`（`:59`）⟹ 变量必须**线性编号**。tableau 的变量是 `(时刻 t, 格子 i)`（外加辅助变量），
编号 `(t,i) ↦ Fin` 要 `_/_`、`_%_` 与单射/往返引理（`decFormula:170` 有除法先例，但方向相反）。

### 3.5 数学硬核：满足赋值 ⟹ 运行存在

「局部子句 ⟹ 全局唯一格局」的提取归纳。这是 CL 的实质内容，**不是工程**：
需要先证「每格恰好一个符号」可从「至少一个 + 至多一个（成对）」推出，再从逐格格局装配出整条运行。
估 300–500 行（含 `Fin`/`Vec` 上的选取引理）。

---

## 四、三件「看起来是资产、其实不是」的事（诚实边界）

### 4.1 `SATLook`（1690 行）不降低 CL 成本

它是**目标端**的机器（把「解 SAT」做成寻址机，代价 `3c·(2m+7)`）。
CL 要构造的是**输入端的归约**（任意验证器 ⟹ 一个 3-CNF 公式）。
两者只在「`runB-+` 拆分 / 相分离 / 尾累积形定义」这类**工程范式**上重叠，**逻辑上无依赖**。

### 4.2 `BooleanSim`（527 行）与 CNF 无关

它是「布尔电路 ⇄ GF(3) 门」的求值等价与账目不放大（W1c 立界定理），不提供公式/子句构造。

### 4.3 `TMBridge`/`TMBridge2`（255+286）是**实例级**

两条都是「单个旗舰语言」的 1 步 / 2 步桥，头注明确不冒充通用桥。
CL 需要的不是桥，而是「给 `InNP` 加机器版」（§3.3）。

---

## 五、路线与代价

| 路线 | 需要的东西 | 估（行，含核对） | 卡点 |
|---|---|---|---|
| **A. 机器版 NP + Cook–Levin tableau** | §3.1+§3.2+§3.3+§3.4+§3.5 全部 | 1800–3000 | §3.5 是数学硬核；§3.1/3.2 是工程沼泽 |
| **B. Fagin（ESO）** | ESO 归译（NP ⟹ ESO 或 ESO ⟹ SAT）+ 模型论公式编码 + 关系猜测 | 2500–4000+ | Fagin 本体本身是 W2 核心；`FMTK-ESO` 只有语义层（280 行），归译为零 |
| **C. 只做 3CNF 化（不做 NP-难）** | §3.1 + Tseitin + 等可满足性 | 300–500 | 无（自足） |

**公共前置**：A 与 C 都需要 §3.1/§3.2 的「一般 CNF + 可构造公式」；A 还需要 §3.3/§3.4/§3.5。
**C 是 A 的真子集**：先做 C，A 的 §3.1/3.2 自动就位。

---

## 六、建议的最小切片（M1）

1. **一般 CNF 层**（新文件 `Complexity/CNF.agda`，估 180–260 行）：
   `Clause' m = List (Lit m)`、`Formula' m = List (Clause' m)`（**不用 Vec**，把长度算术整个绕开）、
   `satClause'`/`satFormula'` + 计账版 + 与 `SATMember` 的 3-CNF 嵌入 `3cnf→cnf` 及语义一致性 `satFormula'-3cnf`。
2. **Tseitin 3CNF 化**（同文件或 `CNF-Tseitin.agda`，估 150–250 行）：
   长子句 ⟹ 辅助变量的 3-子句组；`sat` 双向（满足 ⟹ 存在辅助赋值；存在 ⟹ 满足）+ 规模线性界。
3. **验收判据**：`EXIT=0`、0 postulate / 0 hole、≥ 6 条 `refl` 核对（3-CNF 嵌入、辅助变量、空公式/单子句边界）、
   与 `SATMember.satClause` 在 3-CNF 上逐点一致。

**为什么先做这个**：
- 它是 A 与 C 的公共前置，做了不浪费；
- 它完全绕开 §3.3/§3.4/§3.5 的深水区（不触碰 `InNP`），可独立交付；
- 它同时补掉 `PropositionalLogic` 立界 (iv)（「CNF/范式转换」）这一长期空缺；
- 若最终决定不做 NP-难，M1 仍然是有用资产（任何「一般 CNF 归约到 3-CNF」都需要它）。
