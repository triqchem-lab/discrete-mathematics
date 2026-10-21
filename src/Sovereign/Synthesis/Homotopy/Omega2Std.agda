{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Omega2Std
--
-- **`π₂ᵈˢᵗᵈ` 的平行定义**（人类 2026-10-21 裁决 (b)）
--
-- ## 裁决原文
--
-- > **选 (b)，具体化为「平行定义 `π₂ᵈˢᵗᵈ`，不动 `_PPI5j`」** —— 载体用 `T6CayleySym 1`（已有），
-- > 定义平行于 `π₁ᵈˢᵗᵈ`，验证 `without-k-higher-omega.md` 的三条破法在 `n=2` 上是否也成立。
-- >
-- > **如果成功**，技法可升一层，再考虑 (a)；**如果失败**，失败的具体位置是 (c) 的精确边界。
--
-- ## 本模块（裁决步 1 + 步 3）
--
-- | 步 | 内容 | 状态 |
-- |---|---|---|
-- | **1** | `Ω2WalkStd`：2-走的 **`AStepStd` 版**（平行于 `Omega2.Ω2Walk` 的 `ASTep` 版）+ `Ω2ᵈˢᵗᵈ` 载体 | ✅ |
-- | **3** | 技法验证：`len2s` 定义在**一般索引**上 ⇒ 对数 `Ω2ᵈˢᵗᵈ` 元素**无需 split** | ✅ |
-- | 2 | 类枚举（`nil` 是否孤立、非平凡类是否存在）| ⬜ 见下 |
--
-- ## ★ 关于「商」的一个裁决内选择（已按库内惯例处理）
--
-- 裁决说 `π₂ᵈˢᵗᵈ = Ω²Walk / AHomotopyStd`。本库**不引入 Cubical `_/_`**，
-- 而用 `Sovereign.Foundation.QuotientBasic` 的**无 HIT 商**：
--
-- ```
--   商元素 = 代表元（本模块用 Ω2WalkStd 的项）
--   等价   = 关系本身（与 π₁ᵈˢᵗᵈ 同构：π₁ᵈˢᵗᵈ 也是「走 + AHomotopyStd」而非 HIT）
--   良定义 = Respects（QuotientBasic 已给组合律 resp-id / resp-∘）
-- ```
--
-- 这与 `π₁ᵈˢᵗᵈ` 的处理**一致**（我在 `AStepStdMonoid` 里也是「关系层 + 商面待定」），
-- 且不动 `_PPI5j` ✓。**不引入新机制，不引入 Cubical 商。**
--
-- ## ⚠ 本模块**不**声称
--
--   · `π₂ᵈˢᵗᵈ` 的**群结构**或任何非平凡计算 —— 见步 2 的真实困难（下一个模块）；
--   · `Ω2WalkStd` 与 `Ω2Walk` 的关系（前者步关系更强：`AStep ⊆ AStepStd`）。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `Omega2` 的 `Ω2ᵈ` 名法与 `AStepStd` 的生成元（不重证）

module Sovereign.Synthesis.Homotopy.Omega2Std where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AStep)
open DiGraph using (V; edge)
open import Sovereign.Synthesis.Homotopy.AStepStd using (AStepStd)
open import Sovereign.Synthesis.Homotopy.Omega2 using (Ω2Walk; nil2; cons2; _++2_)

--------------------------------------------------------------------------------
-- §1. `Ω2WalkStd`：2-走，步关系 = `AStepStd`（裁决步 1）
--
-- 与 `Omega2.Ω2Walk` 的唯一差别：步是 `AStepStd`（三角 + 方形 + 回溯）
-- 而不是 `ASTep`（只有三角）。索引仍是**一般变量** ⇒ K 安全 ✓
--------------------------------------------------------------------------------

data Ω2WalkStd (G : DiGraph) (x : V G) : Walk G x x → Walk G x x → Set where
  nil2s  : ∀ (w : Walk G x x) → Ω2WalkStd G x w w
  cons2s : ∀ {w1 w2 w3 : Walk G x x}
         → AStepStd G w1 w2 → Ω2WalkStd G x w2 w3 → Ω2WalkStd G x w1 w3

-- `π₂ᵈˢᵗᵈ` 的载体：常值基点处的闭 2-走
Ω2ᵈˢᵗᵈ : (G : DiGraph) → V G → Set
Ω2ᵈˢᵗᵈ G x = Ω2WalkStd G x (nil x) (nil x)

--------------------------------------------------------------------------------
-- §2. 拼接与幺半群律（平行于 `Omega2._++2_`，结构归纳，K 安全）
--------------------------------------------------------------------------------

infixr 5 _++2s_

_++2s_ : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 : Walk G x x}
       → Ω2WalkStd G x w1 w2 → Ω2WalkStd G x w2 w3 → Ω2WalkStd G x w1 w3
nil2s _      ++2s c' = c'
cons2s s c   ++2s c' = cons2s s (c ++2s c')

++2s-nilR : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
            (c : Ω2WalkStd G x w1 w2) → c ++2s nil2s _ ≡ c
++2s-nilR (nil2s _)     = refl
++2s-nilR (cons2s s c)  = cong (cons2s s) (++2s-nilR c)

++2s-assoc : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 w4 : Walk G x x}
             (c1 : Ω2WalkStd G x w1 w2) (c2 : Ω2WalkStd G x w2 w3)
             (c3 : Ω2WalkStd G x w3 w4)
           → (c1 ++2s c2) ++2s c3 ≡ c1 ++2s (c2 ++2s c3)
++2s-assoc (nil2s _)     c2 c3 = refl
++2s-assoc (cons2s s c)  c2 c3 = cong (cons2s s) (++2s-assoc c c2 c3)

--------------------------------------------------------------------------------
-- §3. ★ 裁决步 3：K 墙破法在 n = 2 上仍成立
--
-- `Ω2ᵈˢᵗᵈ G x = Ω2WalkStd G x (nil x) (nil x)` 两个索引是同一项 ⇒ 对它 split 会撞墙。
-- `len2s` 定义在**一般索引**上 ⇒ split 合法 ✓，`Ω2ᵈˢᵗᵈ` 元素是特例。
--------------------------------------------------------------------------------

len2s : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
      → Ω2WalkStd G x w1 w2 → ℕ
len2s (nil2s _)    = zero
len2s (cons2s _ c) = suc (len2s c)

-- 特例：`Ω2ᵈˢᵗᵈ` 的元素可直接喂进 `len2s`，无需消去 ✓
len2s-at-Ω2ᵈˢᵗᵈ : ∀ {G : DiGraph} {x : V G} → Ω2ᵈˢᵗᵈ G x → ℕ
len2s-at-Ω2ᵈˢᵗᵈ = len2s

--------------------------------------------------------------------------------
-- §4. 两个版本的桥（细关系 ⊆ 新关系的**候选** —— 未证，留作步 2 的前提）
--
-- 直觉：`ASTep ⊆ AStepStd`（`AStepStd.tri-slide` 与 `ASTep.slide` 同形，但 `expand`
-- 在 `AStepStd` 里是 `tri-slide` 的**逆向**，须在闭包层用 `sym` 转）
-- ⇒ `Ω2Walk → Ω2WalkStd` 应当可证，但**本模块未做**（如实标注）。
--
-- 本模块只交付：`Ω2WalkStd` 定义 + 幺半群律 + 技法在 n=2 的验证。
--------------------------------------------------------------------------------
