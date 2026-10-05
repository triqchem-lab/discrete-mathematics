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

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_; _/_; _%_; _<_; _≤_; _>_; NonZero)
open import Data.Nat.DivMod using (m%n<n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (Σ; ∃; _,_)
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

-- 修正：只在未终止（right-top > 0）时证明递减
step-decreases : (s : DayanState) → right-top s > 0 →
                 termination-measure (dayan-step s) < termination-measure s
step-decreases s rt>0 with right-top s | rt>0
... | zero | ()
... | suc rt-1 | _ = m%n<n (right-bottom s) (suc rt-1)
-- 当 right-top = suc rt-1 > 0 时，dayan-step 返回 new_rt = right-bottom s % suc rt-1
-- 由 m%n<n：< suc rt-1

--------------------------------------------------------------------------------
-- §4. 终止性——ℕ 良基归纳
--
--   right-top 严格递减 + ℕ 良基 ⟹ 算法在有限步内终止。
--   终止条件：right-top = 1（奇一而止）。
--
--   完整终止性证明需要良基递归（Acc）或 fuel 参数化——roadmap。
--------------------------------------------------------------------------------

-- fuel 参数化的迭代（dayan-step 已改用模式匹配，不需要 NonZero 约束）
dayan-iterate-fuel : ℕ → DayanState → DayanState
dayan-iterate-fuel zero s = s
dayan-iterate-fuel (suc n) s = dayan-iterate-fuel n (dayan-step s)

-- 终止性陈述（fuel 版）
-- ∃ A P = Σ A P，其中 P : A → Set
termination-statement : Set
termination-statement =
  ∀ (奇 定 : ℕ) →
  Σ ℕ (λ fuel → dayan-terminates (dayan-iterate-fuel fuel (dayan-init 奇 定)))

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
