{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyVecOther
--
-- **`updAt` 不动别的坐标**（`T6CayleyCodeWalk` §7 与 `T6CayleyComm` §3 点名的「⑤ 不同坐标独立」）
--
-- ## 为什么需要
--
-- `π₁ᵈ(T6Cayley n) ≅ (C₃)ⁿ` 的「逐坐标计数」路线要求：沿坐标 `j` 走一步
-- **只改第 `j` 个坐标**。此前库里只有 `updAt-comm`（两个 `updAt` 可交换），
-- 但**没有**「`lookup i (updAt j v) ≡ lookup i v`（当 `i ≢ j`）」这一条。
--
-- ## 证法
--
-- 直接对 `Fin` 构造子分情况（`updAt` 的定义就是按 `Fin` 递归的）：
--   · `zero` vs `zero` ⇒ 与 `i ≢ j` 矛盾
--   · `zero` vs `suc`  ⇒ 两边都得 `a` ⇒ `refl`
--   · `suc`  vs `zero` ⇒ 两边都得 `lookup v i'` ⇒ `refl`
--   · `suc`  vs `suc`  ⇒ 归纳假设
--
-- ## 核心原则
--   · 0 postulate / 0 hole；复用 `updAt`（不重写）

module Sovereign.Synthesis.Homotopy.T6CayleyVecOther where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; _∷_; lookup)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec; updAt)

--------------------------------------------------------------------------------
-- ★ `updAt j` 不改坐标 `i`（当 `i ≢ j`）
--------------------------------------------------------------------------------

updAt-other : ∀ {n : ℕ} (i j : Fin n) (v : T6Vec n)
            → ¬ (i ≡ j) → lookup (updAt j v) i ≡ lookup v i
updAt-other Fin.zero    Fin.zero    (a ∷ v) i≢j = ⊥-elim (i≢j refl)
updAt-other Fin.zero    (Fin.suc j) (a ∷ v) _   = refl
updAt-other (Fin.suc i) Fin.zero    (a ∷ v) _   = refl
updAt-other (Fin.suc i) (Fin.suc j) (a ∷ v) i≢j =
  updAt-other i j v (λ i≡j → i≢j (cong Fin.suc i≡j))
