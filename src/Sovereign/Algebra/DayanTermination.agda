{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DayanTermination
-- 大衍求一术 S-D3 终止性定理——right-top 递减 + 良基归纳
--
-- 数学内容：
--   终止性由 right-top 的严格递减保证：
--     right-top (dayan-step s) = right-bottom s % right-top s < right-top s
--   这是 stdlib 的 m%n < n（当 n > 0）。
--   ℕ 的良基归纳给出算法终止。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.DayanTermination where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_; _/_; _%_; _<_; _≤_; NonZero)
open import Data.Nat.DivMod using (m%n<n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

--------------------------------------------------------------------------------
-- §1. DayanState 引入
--------------------------------------------------------------------------------

open import Sovereign.Algebra.DayanState
  using (DayanState; dayan; dayan-init; dayan-step; dayan-terminates;
         left-top; left-bottom; right-top; right-bottom)

--------------------------------------------------------------------------------
-- §2. 终止性度量——right-top
--------------------------------------------------------------------------------

termination-measure : DayanState → ℕ
termination-measure = right-top

--------------------------------------------------------------------------------
-- §3. 步后 right-top 递减
--
--   dayan-step 中 new_rt = right-bottom s % right-top s
--   由 stdlib 的 m%n<n：当 right-top s > 0 时，new_rt < right-top s
--------------------------------------------------------------------------------

step-decreases : (s : DayanState) → ⦃ _ : NonZero (right-top s) ⦄ →
                 termination-measure (dayan-step s) < termination-measure s
step-decreases s = m%n<n (right-bottom s) (right-top s)
-- dayan-step 的 new_rt = right-bottom s % right-top s
-- 由 m%n<n：< right-top s

--------------------------------------------------------------------------------
-- §4. 终止性——ℕ 良基归纳
--
--   right-top 严格递减 + ℕ 良基 ⟹ 算法在有限步内终止。
--   终止条件：right-top = 1（奇一而止）。
--
--   完整终止性证明需要良基递归（Acc）或 fuel 参数化——roadmap。
--------------------------------------------------------------------------------

-- 终止性陈述（类型签名——roadmap）
-- termination-statement : ∀ (奇 定 : ℕ) →
--   ∃ ℕ (λ n → dayan-terminates (dayan-iterate n (dayan-init 奇 定)))
--   其中 dayan-iterate 需要 NonZero 约束（S-D3 核心问题）

--------------------------------------------------------------------------------
-- §5. S-D3 完成度
--
--   ✅ step-decreases：right-top 严格递减（m%n<n）
--   ⚠ termination-statement：需要良基递归或 fuel（roadmap）
--
--   step-decreases 已闭合——这正是 L2 step-invariant 的 NonZero 约束来源。
--   当 right-top s > 0 时，dayan-step 可执行，且 right-top 递减。
--   ℕ 的良基性保证算法终止。
--------------------------------------------------------------------------------
