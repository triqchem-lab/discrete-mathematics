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

## 八、维护约定

1. **新增 proven 时**：在本清单对应章节加一行（符号 + 命题 + 回执）
2. **撤回时**：**不删除** ✓ —— 标 ⚠ 并写撤回理由（台账只增不改史 ✓）
3. **本文件与台账冲突时**：**以台账为准** ✓（`proof_dag` 是机器权威 ✓）
