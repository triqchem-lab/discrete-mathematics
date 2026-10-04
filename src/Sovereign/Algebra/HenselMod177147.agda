{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMod177147
-- 任务书第三层·3.2 延伸：mod 177147 的 x² ≡ 1 根全景（p = 3¹¹ 实例）
--
-- mod 59049 根 x ≡ 1, 59048 各提升三候选（+59049k）：
--   x ≡ 1 ↦ {1, 59050, 118099}；x ≡ 59048 ↦ {59048, 118097, 177146}
--   根：x = 1, x = 177146。非根：x = 59050/118099/59048/118097。
--   ⟹ mod 177147 根全景：恰 {1, 177146}。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselMod177147 where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; _≤_)
open import Data.Empty using (⊥)
open import Data.Nat.Divisibility
  using (_∣_; ∣m+n∣m⇒∣n; ∣⇒≤; n∣m*n)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Algebra.HenselLiftUniqueness using (≤<-asym; 1+<-trans)

∣177147-step : ∀ {m r : ℕ} → 177147 ∣ (m + r) → 177147 ∣ m → 177147 ∣ r
∣177147-step = ∣m+n∣m⇒∣n

-- x = 59050 : 59050²-1 = 3486902499 = 19683·177147 + 118098
¬177147∣3486902499 : ¬ (177147 ∣ 3486902499)
¬177147∣3486902499 h =
  ≤<-asym 177147 118098
    (∣⇒≤ (∣177147-step h (n∣m*n 19683)))
    (1+<-trans 59048 118098)

-- x = 118099 : 118099²-1 = 13947373800 = 78733·177147 + 59049
¬177147∣13947373800 : ¬ (177147 ∣ 13947373800)
¬177147∣13947373800 h =
  ≤<-asym 177147 59049
    (∣⇒≤ (∣177147-step h (n∣m*n 78733)))
    (1+<-trans 118097 59049)

-- x = 59048 : 59048²-1 = 3486666303 = 19682·177147 + 59049
¬177147∣3486666303 : ¬ (177147 ∣ 3486666303)
¬177147∣3486666303 h =
  ≤<-asym 177147 59049
    (∣⇒≤ (∣177147-step h (n∣m*n 19682)))
    (1+<-trans 118097 59049)

-- x = 118097 : 118097²-1 = 13946901408 = 78730·177147 + 118098
¬177147∣13946901408 : ¬ (177147 ∣ 13946901408)
¬177147∣13946901408 h =
  ≤<-asym 177147 118098
    (∣⇒≤ (∣177147-step h (n∣m*n 78730)))
    (1+<-trans 59048 118098)

root-1 : 177147 ∣ 0
root-1 = n∣m*n 0

root-177146 : 177147 ∣ 31380705315
root-177146 = n∣m*n 177145
