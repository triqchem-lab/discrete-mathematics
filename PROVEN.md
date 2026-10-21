# PROVEN.md — 已证清单（防重复实现）

> **用途**：写任何「新」定理 / record / 实例**之前**，先读本清单 + 跑 `proof_dag action:"search"`。
> **为什么存在**：本会话实测**三次重复实现**（`DCPresentation.agda` / `dc-oblivion-*` / 「全库第一个 Presentation」），
> 根因是「`bash grep` 只查单个文件」+「长会话忘记前面证过什么」。
>
> **本清单是人工维护的「最近 / 最常复用」子集**（全库 771 条 proven 在台账里，不在此重复）：
> - 权威全量：`proof_dag action:"list"`（或 `~/.dsh/state/math-proof/dag-11083e096b45.json`）
> - 按关键词查：`proof_dag action:"search" query:"…"`
> - 按模块查：DSH `grep` 工具（ripgrep 语法）

---

## 一、检索纪律（硬性前置，不是建议）

| 场景 | 强制动作 |
|---|---|
| 写任何「新」定理 | **先** `proof_dag action:"search"` + **DSH grep 全库** `src/Sovereign` |
| 写任何「新」record / 实例 | 同上（尤其是 `record X : Set` / `X : SomeRecord`） |
| 搜索任何概念 | **DSH `grep` 工具**（ripgrep 语法），**不用** `bash grep` 单文件 |

**⇒ 已由机器强制**：`.git/hooks/pre-commit` → `engineering/check_duplicate.sh`（提交前拦重复符号）

---

## 二、零冥族归零（**本地早已完成**，不是新增）

### `ZeroOblivion`（`src/Sovereign/Algebra/GroupTheory/DuodecClock.agda:504`）

| 字段 | 命题 |
|---|---|
| `addZeroR` | `∀ x → mixedOp x zero ≡ x` |
| `addZeroL` | `∀ x → mixedOp zero x ≡ x` |
| `mulAlphaCycle` | `mulAlpha (mulAlpha (mulAlpha a1 a1) a1) a1 ≡ a0`（α⁴ = 1） |
| `tritCycle` | `∀ x → (x ⊕ x) ⊕ x ≡ T₀`（⊕³ = 0） |
| `jointCycle` | `∀ p → mixedOp^12 p ≡ p`（mixedOp¹² = id） |

**实例**：
- `zero-oblivion-instance : ZeroOblivion`（`DuodecClock.agda:673`）
- `dcZeroOblivion : ZeroOblivion`（`DCGroup.agda:153`，第二份）
- `zero-oblivion-to-d0 : toDuodec duodec-e ≡ d0`（`DuodecClock.agda:870`）

**⚠ 别重复实现**：本会话曾写 `dc-oblivion-trit/-phase/-joint` ✗ —— 全部是这三条的重复 ✗（已删除）

---

## 三、Trit 加法归零（`src/Sovereign/Base/Trit.agda`）

| 符号 | 命题 |
|---|---|
| `verifyZero`（:277） | `T₁ ⊕ T₂ ≡ T₀` |
| `verifyMul`（:281） | `T₂ ⊗ T₂ ≡ T₁` |
| `⊕-inverse`（:232） | `∀ x → x ⊕ negate x ≡ T₀` |
| `negate-equiv` | 逐元素取反表 |

---

## 四、展示群模板层（`PresentationTheorems.agda`）

### `g-ne-unit`（**回执 `fe46503a`**）

```agda
g-ne-unit : ∀ {A} (P : Presentation A)
  (0<clk : 0 < clock)
  (1<po  : 1 < phase-order)
  (clock-min : ∀ k → Period (λ y → step y g) k → clock ∣ k)
  (po∣clk    : phase-order ∣ clock)
  → g ≢ unit
```

**普遍定理** ✓ —— 不依赖 DC 的任何特殊结构 ✓
**证明**：若 `g = unit` ⇒ `step y g = y`（`zeroʳ`）⇒ `1` 是周期 ⇒ `clock ∣ 1` ⇒ `clock ≤ 1` ✗
但 `1 < phase-order ≤ clock` ⇒ `clock ≥ 2` ✗ 矛盾 ✓

---

## 五、DC 特有定理（**不写进通用模板** ✗，`Presentation.agda` 末尾，回执 `9e2e0966`）

| 符号 | 命题 | 缺口 |
|---|---|---|
| `dc-phase-step-comm` | `∀ x y → dc-phase (mixedOp x y) ≡ mixedOp (dc-phase x) y` | G3 |
| `dc-phase-g-comm` | `∀ x → dc-phase (mixedOp (T₁,a₁) x) ≡ mixedOp (T₁,a₁) (dc-phase x)` | N8 |
| `dc-clock-neq-phase` | `4 < 12` | N3b |
| `dc-oblivion-algebra` | `T₁ ⊕ T₂ ≡ T₀`（= `verifyZero` 引用，非新增） | 代数归零 |

**⚠ 这些不是普遍约束** ✗ —— 当前 `Presentation` 模板**没有字段**连接 `phase` 与 `step` ✗
（写进模板 = 过拟合 DC ✗ —— 见 `docs/duodecimal/42-presentation-group-definition.md` §4.2）

---

## 六、T4 主线（`GF3HammingCount` 家族）

| 模块 | 关键定理 | 回执 |
|---|---|---|
| `Algebra/LinearAlgebra/GF3HammingCount.agda`（1206 行） | `★a-binomial : C0 n ≡ S'' fzero n`<br>`★b-formula : (S'' fzero n ∸ Z n) + Z n ≡ C0 n`<br>`★C0-3step` / `★C0-odd` | `da832222` |
| `Algebra/LinearAlgebra/GF3HammingCountLink.agda`（158 行） | `★Cnt : ∀ r n → Cnt r n ≡ Cr r n`<br>`★C0-is-hamming : ∀ n → Cnt fzero n ≡ C0 n` | `a2d87388` |
| `Algebra/LinearAlgebra/GF9KernelImageZero.agda` | `q-zero : Ker f → Im f → ∀ x → f x ≡ gf9-zero`（`q_n = 0`） | `4dcfbb13` |
| `Algebra/LinearAlgebra/GF3BnLinearAlgebra.agda`（161 行） | `★AllH : ∀ n → AllH fzero n ≡ Z n` | `4eb44d77` |
| `Algebra/UniversalAlgebra/RnDCPresentation.agda`（143 行） | `RnDCPresentation : (n : ℕ) → Presentation (RD n)`（`clock = 12` ✓） | `647efff9` |

**⚠ 已撤回**：`RnPresentation.agda`（`clock = 4 = phase-order` ✗ 踩 DC 红线 ✗，节点标 `needs_review`）

---

## 七、Presentation 模板的三个实例

| 实例 | 载体 | `clock` | 合法？ |
|---|---|---|---|
| `dc-presentation`（`Presentation.agda:131`） | `DuodecPoint` | 12 | ✅ **本源实例** |
| `RnDCPresentation`（`RnDCPresentation.agda:127`） | `Vec DuodecPoint (3^n)` | 12 | ✅ |
| `RnPresentation`（`RnPresentation.agda:126`） | `Vec GF9 (3^n)` | **4** | ❌ **已撤回**（`clock = phase-order` ✗） |

**⚠ 索引工具只看「字段齐全」✗ —— 语义红线要人工判** ✓
（`engineering/index_presentations.sh` 的免责声明即为此而写）

---

## 八、高阶同伦线 · `π₂ᵈ⁺`（`src/Sovereign/Synthesis/Homotopy/`，2026-10-21 建线）

> **本节只写「有内核回执」的事实**（符号 + 命题 + 回执）。
> 路线判断一律不写 —— 见 `AGENTS.md`「★★ 路线判断也要标推测」。

### 8.1 定义层 → 群结构

| 模块 | 关键符号 | 回执 |
|---|---|---|
| `Omega2.agda` | `Ω1ᵈ` / `Ω2Walk`（`nil2`/`cons2`）/ `Ω2ᵈ` / `_++2_` / `++2-assoc` | `72d0eecf` |
| `Omega3.agda` | `invAStep` / `invAStep-invol` / `Ω3Step`（`fill-tri`）/ `Ω3Walk` / `Ω3ᵈ` | `31bc258e` |
| `Omega3Plus.agda` | `bub` / `Ω3Step⁺` / `embed3` / **`base3+-redundant`**（`base3+` 可由 `bub3` 导出 ⇒ 生成集可缩到 `{whisk3, bub3}`） | `f0fc1f7a` |
| `Omega3Suffix.agda` | `whisk-resp` / `suffix-resp` / **`≡→Ω3Walk⁺`**（propEq → 关系的零成本桥） | `62112afd` |
| `Omega2Reverse.agda` | `rev2` / `rev2-cancel` / **`suffix-cancel`**（带上下文的反向消去） | `b550e39c` |
| `Omega2ReverseInvol.agda` | `rev2-dist` / **`rev2-invol`** / `inv-right-Ω3` | `f76b17cc` |
| `Omega2Std.agda` | `Ω2WalkStd` / `Ω2ᵈˢᵗᵈ` / `++2s-nilR` / `++2s-assoc` | `403e74b1` |
| **`Pi2dFunctionLayer.agda`** | **★ `π₂ᵈ⁺` 是群**（函数表示层，零 Cubical）：`unit-left` / `unit-right` / `assoc-Ω3` / `cong₂-Ω3` / `inv-left-Ω3` / `inv-left-ctx` | `037128ec` |

### 8.2 不变量 → 非平凡性 → 群同态

| 模块 | 关键符号 | 回执 |
|---|---|---|
| `Pi2dParity.agda` | `par2`（步数奇偶）/ **`par2-Walk⁺`**（奇偶是良定义的**类函数**＝分裂器）/ `two-classes`（有自步时**至少**两类） | `0e9a7aa2` |
| `Pi2dWinding.agda` | `wstep`（`slide ↦ +1`、`expand ↦ −1`）/ `wind` / **`wind-bub`**（气泡位移 = 0）/ `wind-Walk⁺` / **★ `no-collapse`**（不同层数不同类 ⇒ **无穷多类**） | `206dc30e` |
| `Pi2dWindingRev.agda` | `wstep-inv-sum` / `rev2-wind-form` / **★ `wind-rev2`**（`wind (rev2 c) + wind c ≡ +0`）⇒ **`wind : π₂ᵈ⁺ →+ ℤ` 是群同态** | `0159b507` |

### 8.3 商路线（另一条，保留）

| 模块 | 关键符号 | 回执 |
|---|---|---|
| `Pi2dQuotient.agda` | `π₂ᵈ` / `π₂ᵈ⁺` / `[_]ᵈ` / `desc` / `π₂ᵈ-hom` / `addL`·`addR` + 结合律（`_/_` 商路线，含 `SetQuotient`） | `113f4102` |

### 8.4 码层（`T6Cayley`，**无证明分量**）

| 模块 | 关键符号 | 回执 |
|---|---|---|
| `T6CayleyDec.agda` | `DecEq-T6Vec`（`Vec (Fin 3) n` 可判定）/ `decAt` / `decAt2` / `findEdge`（`Maybe`，带见证）/ `∈-allFinD`（穷尽性） | `30333b2f` |
| `T6CayleyCode.agda` | `CStep`（`cplus`/`cminus`，**无证明分量**）/ `CWalk` / `DecEq-CStep` / `DecEq-CWalk`（平凡，**不用 uip**）/ **`creduce`**（fuel 递归消相邻逆对） | `a3664bd1` |
| `T6CayleyCodeWalk.agda` | `ctarget` / **`cEdge`（见证 = `refl`，无需搜索）** / `interpC` / `ctarget-inv` / **`ctarget-3`**（每步 3 阶）/ `foldT` / `foldT-++` / `crev` / **`ctarget-rev`**（逆律） | `f07cfdae` |
| `T6CayleyComm.agda` | **`updAt-comm`**（`updAt i` 与 `updAt j` 交换 ⇒ **`(C₃)ⁿ` 作为群 Abel**） | `4ae7a0a7` |

### 8.5 ⚠ 已撤回 / 未验证（**别当成已证复用**）

| 曾声称 | 现状 |
|---|---|
| `π₂ᵈ⁺` **至多两类**（⇒ 或 ≅ C₂） | ❌ **已撤回**。`par2-Walk⁺` 只给「良定义」；**良定义 ≠ 单射**，拿不到上界。 |
| `Ω2Walk G x w1 w2` 只在 `w1`、`w2` 相等时可居留 | ❌ **已撤回**。`cons2 s (nil2 w2)` 就是 `w1 ≢ w2` 的居留者。 |
| `π₁ᵈ(T6Cayley n) ≅ (C₃)ⁿ`，「五项前置已齐，只差一项」 | ❌ **路线判断已撤回**：该「差距分析」本身未核实。**已证的只有** 8.4 表里的那些符号。 |
| `creduce` 的完备性 / 汇合性 | ⬜ **未做**。`creduce` 的 `no` 分支不重查头部 ⇒ 一遍不保证到不动点。 |
| `π₂ᵈ⁺` 的精确刻画（≅ 自由群？） | ⬜ **未做**，且形状问题未定（需 `DecEq` 或汇合性；`ASTep` 含见证 ⇒ 一般图不可判定）。 |

**⚠ 层级提醒（已核实）**：`Ω2Walk` 的步是 **`ASTep`（一阶同伦）**，不是图边；
而 `CStep` 是**图边方向** ⇒ **码层服务 `π₁ᵈ` 层，不是 `π₂ᵈ⁺` 层**。

---

## 九、维护约定

1. **新增 proven 时**：在本清单对应章节加一行（符号 + 命题 + 回执）
2. **撤回时**：**不删除** ✓ —— 标 ⚠ 并写撤回理由（台账只增不改史 ✓）
3. **本文件与台账冲突时**：**以台账为准** ✓（`proof_dag` 是机器权威 ✓）
