{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMod6561
-- 任务书第三层·3.2 延伸：mod 6561 的 x² ≡ 1 根全景（p = 3⁸ 实例）
--
-- mod 2187 根 x ≡ 1, 2186 各提升三候选（+2187k）：
--   x ≡ 1 ↦ {1, 2188, 4375}；x ≡ 2186 ↦ {2186, 4374, 6560}
--   根：x = 1, x = 6560。非根：x = 2188/4375/2186/4374。
--   ⟹ mod 6561 根全景：恰 {1, 6560}。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselMod6561 where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; _≤_)
open import Data.Empty using (⊥)
open import Data.Nat.Divisibility
  using (_∣_; ∣m+n∣m⇒∣n; ∣⇒≤; n∣m*n)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Algebra.HenselLiftUniqueness using (≤<-asym; 1+<-trans)

∣6561-step : ∀ {m r : ℕ} → 6561 ∣ (m + r) → 6561 ∣ m → 6561 ∣ r
∣6561-step = ∣m+n∣m⇒∣n

-- x = 2188 : 2188²-1 = 4787343 = 4782969 + 4374（4782969 = 729·6561）
¬6561∣4787343 : ¬ (6561 ∣ 4787343)
¬6561∣4787343 h =
  ≤<-asym 6561 4374
    (∣⇒≤ (∣6561-step h (n∣m*n 729)))
    (1+<-trans 2186 4374)

-- x = 4375 : 4375²-1 = 19140624 = 19138437 + 2187（19138437 = 2917·6561）
¬6561∣19140624 : ¬ (6561 ∣ 19140624)
¬6561∣19140624 h =
  ≤<-asym 6561 2187
    (∣⇒≤ (∣6561-step h (n∣m*n 2917)))
    (1+<-trans 4373 2187)

-- x = 2186 : 2186²-1 = 4778595 = 4776408 + 2187（4776408 = 728·6561）
¬6561∣4778595 : ¬ (6561 ∣ 4778595)
¬6561∣4778595 h =
  ≤<-asym 6561 2187
    (∣⇒≤ (∣6561-step h (n∣m*n 728)))
    (1+<-trans 4373 2187)

-- x = 4374 : 4374²-1 = 19131875 = 19125315 + 6560（19125315 = 2915·6561）
¬6561∣19131875 : ¬ (6561 ∣ 19131875)
¬6561∣19131875 h =
  ≤<-asym 6561 6560
    (∣⇒≤ (∣6561-step h (n∣m*n 2915)))
    (1+<-trans 0 6560)

root-1 : 6561 ∣ 0
root-1 = n∣m*n 0

root-6560 : 6561 ∣ 43033599
root-6560 = n∣m*n 6559
