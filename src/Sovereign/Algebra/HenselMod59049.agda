{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMod59049
-- 任务书第三层·3.2 延伸：mod 59049 的 x² ≡ 1 根全景（p = 3¹⁰ 实例）
--
-- mod 19683 根 x ≡ 1, 19682 各提升三候选（+19683k）：
--   x ≡ 1 ↦ {1, 19684, 39367}；x ≡ 19682 ↦ {19682, 39365, 59048}
--   根：x = 1, x = 59048。非根：x = 19684/39367/19682/39365。
--   ⟹ mod 59049 根全景：恰 {1, 59048}。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselMod59049 where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; _≤_)
open import Data.Empty using (⊥)
open import Data.Nat.Divisibility
  using (_∣_; ∣m+n∣m⇒∣n; ∣⇒≤; n∣m*n)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Algebra.HenselLiftUniqueness using (≤<-asym; 1+<-trans)

∣59049-step : ∀ {m r : ℕ} → 59049 ∣ (m + r) → 59049 ∣ m → 59049 ∣ r
∣59049-step = ∣m+n∣m⇒∣n

-- x = 19684 : 19684²-1 = 387459855 = 6561·59049 + 39366
¬59049∣387459855 : ¬ (59049 ∣ 387459855)
¬59049∣387459855 h =
  ≤<-asym 59049 39366
    (∣⇒≤ (∣59049-step h (n∣m*n 6561)))
    (1+<-trans 19682 39366)

-- x = 39367 : 39367²-1 = 1549760688 = 26245·59049 + 19683
¬59049∣1549760688 : ¬ (59049 ∣ 1549760688)
¬59049∣1549760688 h =
  ≤<-asym 59049 19683
    (∣⇒≤ (∣59049-step h (n∣m*n 26245)))
    (1+<-trans 39365 19683)

-- x = 19682 : 19682²-1 = 387381123 = 6560·59049 + 19683
¬59049∣387381123 : ¬ (59049 ∣ 387381123)
¬59049∣387381123 h =
  ≤<-asym 59049 19683
    (∣⇒≤ (∣59049-step h (n∣m*n 6560)))
    (1+<-trans 39365 19683)

-- x = 39365 : 39365²-1 = 1549603224 = 26242·59049 + 39366
¬59049∣1549603224 : ¬ (59049 ∣ 1549603224)
¬59049∣1549603224 h =
  ≤<-asym 59049 39366
    (∣⇒≤ (∣59049-step h (n∣m*n 26242)))
    (1+<-trans 19682 39366)

root-1 : 59049 ∣ 0
root-1 = n∣m*n 0

root-59048 : 59049 ∣ 3486666303
root-59048 = n∣m*n 59047
