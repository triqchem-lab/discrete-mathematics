{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMod19683
-- 任务书第三层·3.2 延伸：mod 19683 的 x² ≡ 1 根全景（p = 3⁹ 实例）
--
-- mod 6561 根 x ≡ 1, 6560 各提升三候选（+6561k）：
--   x ≡ 1 ↦ {1, 6562, 13123}；x ≡ 6560 ↦ {6560, 13121, 19682}
--   根：x = 1, x = 19682。非根：x = 6562/13123/6560/13121。
--   ⟹ mod 19683 根全景：恰 {1, 19682}——与奇 p 幂理论一致。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselMod19683 where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; _≤_)
open import Data.Empty using (⊥)
open import Data.Nat.Divisibility
  using (_∣_; ∣m+n∣m⇒∣n; ∣⇒≤; n∣m*n)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Algebra.HenselLiftUniqueness using (≤<-asym; 1+<-trans)

∣19683-step : ∀ {m r : ℕ} → 19683 ∣ (m + r) → 19683 ∣ m → 19683 ∣ r
∣19683-step = ∣m+n∣m⇒∣n

-- x = 6562 : 6562²-1 = 43059843 = 2187·19683 + 13122
¬19683∣43059843 : ¬ (19683 ∣ 43059843)
¬19683∣43059843 h =
  ≤<-asym 19683 13122
    (∣⇒≤ (∣19683-step h (n∣m*n 2187)))
    (1+<-trans 6560 13122)

-- x = 13123 : 13123²-1 = 172213128 = 8749·19683 + 6561
¬19683∣172213128 : ¬ (19683 ∣ 172213128)
¬19683∣172213128 h =
  ≤<-asym 19683 6561
    (∣⇒≤ (∣19683-step h (n∣m*n 8749)))
    (1+<-trans 13121 6561)

-- x = 6560 : 6560²-1 = 43033599 = 2186·19683 + 6561
¬19683∣43033599 : ¬ (19683 ∣ 43033599)
¬19683∣43033599 h =
  ≤<-asym 19683 6561
    (∣⇒≤ (∣19683-step h (n∣m*n 2186)))
    (1+<-trans 13121 6561)

-- x = 13121 : 13121²-1 = 172160640 = 8746·19683 + 13122
¬19683∣172160640 : ¬ (19683 ∣ 172160640)
¬19683∣172160640 h =
  ≤<-asym 19683 13122
    (∣⇒≤ (∣19683-step h (n∣m*n 8746)))
    (1+<-trans 6560 13122)

root-1 : 19683 ∣ 0
root-1 = n∣m*n 0

root-19682 : 19683 ∣ 387381123
root-19682 = n∣m*n 19681
