{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMod2187
-- 任务书第三层·3.2 延伸：mod 2187 的 x² ≡ 1 根全景（p = 3⁷ 实例）
--
-- 数学背景：mod 729 根 x ≡ 1, 728（±1 mod 729）各提升三候选（+729k）：
--   x ≡ 1 ↦ {1, 730, 1459}；x ≡ 728 ↦ {728, 1457, 2186}
--   根：x = 1, x = 2186。非根：x = 730/1459/728/1457。
--   ⟹ mod 2187 根全景：恰 {1, 2186}——与奇 p 幂理论一致。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselMod2187 where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; _≤_)
open import Data.Empty using (⊥)
open import Data.Nat.Divisibility
  using (_∣_; ∣m+n∣m⇒∣n; ∣⇒≤; n∣m*n)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Algebra.HenselLiftUniqueness using (≤<-asym; 1+<-trans)

∣2187-step : ∀ {m r : ℕ} → 2187 ∣ (m + r) → 2187 ∣ m → 2187 ∣ r
∣2187-step = ∣m+n∣m⇒∣n

-- x = 730 : 730²-1 = 532899 = 531441 + 1458（531441 = 243·2187）
¬2187∣532899 : ¬ (2187 ∣ 532899)
¬2187∣532899 h =
  ≤<-asym 2187 1458
    (∣⇒≤ (∣2187-step h (n∣m*n 243)))
    (1+<-trans 728 1458)

-- x = 1459 : 1459²-1 = 2128680 = 2127951 + 729（2127951 = 973·2187）
¬2187∣2128680 : ¬ (2187 ∣ 2128680)
¬2187∣2128680 h =
  ≤<-asym 2187 729
    (∣⇒≤ (∣2187-step h (n∣m*n 973)))
    (1+<-trans 1457 729)

-- x = 728 : 728²-1 = 529983 = 529254 + 729（529254 = 242·2187）
¬2187∣529983 : ¬ (2187 ∣ 529983)
¬2187∣529983 h =
  ≤<-asym 2187 729
    (∣⇒≤ (∣2187-step h (n∣m*n 242)))
    (1+<-trans 1457 729)

-- x = 1457 : 1457²-1 = 2122848 = 2121390 + 1458（2121390 = 970·2187）
¬2187∣2122848 : ¬ (2187 ∣ 2122848)
¬2187∣2122848 h =
  ≤<-asym 2187 1458
    (∣⇒≤ (∣2187-step h (n∣m*n 970)))
    (1+<-trans 728 1458)

-- 正根
root-1 : 2187 ∣ 0
root-1 = n∣m*n 0

root-2186 : 2187 ∣ 4778595
root-2186 = n∣m*n 2185
