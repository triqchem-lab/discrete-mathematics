{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselLiftMod27
-- 任务书第三层·3.2 收官：mod 27 唯一性——四非根见证全闭合
--
-- 数学背景：mod 9 的两个根 x ≡ 1 与 x ≡ 8 提升到 mod 27 各有三候选，
--   恰一成功（x=1 与 x=26，正见证在 Tower）：
--     x ≡ 1: {1, 10, 19} —— 27∣0 ✓, ¬(27∣99), ¬(27∣360)
--     x ≡ 8: {8, 17, 26} —— ¬(27∣63), ¬(27∣288), 27∣675 ✓
--
-- 技术要点（商枚举的彻底消除）：R12/R14 的逐商 ≤<-asym 路线被
--   stdlib 的 **∣m+n∣m⇒∣n** 一步替代——
--     63 = 54 + 9, 27∣54（n∣m*n 2）⟹ 27∣9；再 ∣⇒≤ : 27 ≤ 9，
--     与 9 < 27（1+<-trans 链）经 ≤<-asym 导出 ⊥。
--   四否定同构，零 case 分析、零递归引理。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselLiftMod27 where

open import Data.Nat using (ℕ; _+_; _*_; _∸_; _≤_; _<_)
open import Data.Nat.Base using (NonZero)
open import Data.Product using (proj₂)
open import Data.Empty using (⊥)
open import Data.Nat.Divisibility
  using (_∣_; ∣m+n∣m⇒∣n; ∣⇒≤; n∣m*n)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Sovereign.Algebra.HenselLiftUniqueness using (≤<-asym; 1+<-trans)

--------------------------------------------------------------------------------
-- §1. 泛型一步消去：d∣(m+n) ∧ d∣m ⟹ d∣n ⟹ d≤n ⟹ 与 n<d 矛盾
--------------------------------------------------------------------------------

∣27-elim : ∀ m n → ⦃ NonZero n ⦄ → 27 ∣ (m + n) → 27 ∣ m → n < 27 → ⊥
∣27-elim m n h d∣m n<27 = ≤<-asym 27 n (∣⇒≤ d∣n) n<27
  where
    d∣n : 27 ∣ n
    d∣n = ∣m+n∣m⇒∣n h d∣m

-- 数值锚（refl 计算闭合）
63≡54+9 : 63 ≡ 54 + 9
63≡54+9 = refl

99≡81+18 : 99 ≡ 81 + 18
99≡81+18 = refl

288≡270+18 : 288 ≡ 270 + 18
288≡270+18 = refl

360≡351+9 : 360 ≡ 351 + 9
360≡351+9 = refl

--------------------------------------------------------------------------------
-- §2. 四非根见证
--------------------------------------------------------------------------------

-- x = 8：8² - 1 = 63 = 54 + 9 → 27∣9 → 27 ≤ 9 与 9 < 27 矛盾
¬27∣63 : ¬ (27 ∣ 63)
¬27∣63 h = ∣27-elim 54 9 h (n∣m*n 2) (1+<-trans 17 9)

-- x = 10：10² - 1 = 99 = 81 + 18 → 27∣18 → 27 ≤ 18 与 18 < 27 矛盾
¬27∣99 : ¬ (27 ∣ 99)
¬27∣99 h = ∣27-elim 81 18 h (n∣m*n 3) (1+<-trans 8 18)

-- x = 17：17² - 1 = 288 = 270 + 18 → 27∣18 → 矛盾
¬27∣288 : ¬ (27 ∣ 288)
¬27∣288 h = ∣27-elim 270 18 h (n∣m*n 10) (1+<-trans 8 18)

-- x = 19：19² - 1 = 360 = 351 + 9 → 27∣9 → 矛盾
¬27∣360 : ¬ (27 ∣ 360)
¬27∣360 h = ∣27-elim 351 9 h (n∣m*n 13) (1+<-trans 17 9)

--------------------------------------------------------------------------------
-- §3. 正见证（复用）
--------------------------------------------------------------------------------

import Sovereign.Algebra.HenselLiftTower as Tower

lift-1-mod-27 : 27 ∣ ((1 * 1) ∸ 1)
lift-1-mod-27 = proj₂ (proj₂ Tower.tower-1)

lift-26-mod-27 : 27 ∣ ((26 * 26) ∸ 1)
lift-26-mod-27 = proj₂ (proj₂ Tower.tower-26)
