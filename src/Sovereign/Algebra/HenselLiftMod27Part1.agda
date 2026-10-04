{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselLiftMod27Part1
-- 任务书第三层·3.2 深化：mod 27 唯一性 part 1——小商非根见证
--
-- 数学背景：R7/R12/R13 闭合了 mod 9 的 Hensel 全景。本模块启动 mod 27
--   唯一性：mod 9 的根 x ≡ 1 提升候选 x ∈ {1, 10, 19}、根 x ≡ 8 提升候选
--   x ∈ {8, 17, 26}。本模块闭合两个**小商非根**见证：
--     x = 8：8² - 1 = 63 = 2·27 + 9 → ¬(27∣63)
--     x = 10：10² - 1 = 99 = 3·27 + 18 → ¬(27∣99)
--   （大商 ¬(27∣288)、¬(27∣360) 与正见证 27∣675 下轮/已有）
--
-- 复用：R12 的 ≤<-asym / 1+<-trans（零重写导入）。
--
-- 技术要点：q ≥ 3（q·27 ≥ 81 > 63）与 q ≥ 4（q·27 ≥ 108 > 99）的
--   下界经递归引理 81≤/108≤（base ≤-refl 计算 + step m≤n+m），矛盾经
--   ≤-trans 汇入 ≤<-asym（cubical 安全）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselLiftMod27Part1 where

open import Data.Nat using (ℕ; zero; suc; _*_; _≤_; z≤n; s≤s)
open import Data.Empty using (⊥)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; m≤n+m; <-trans)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)
open import Sovereign.Algebra.HenselLiftUniqueness using (≤<-asym; 1+<-trans)

--------------------------------------------------------------------------------
-- §1. 递归下界引理
--------------------------------------------------------------------------------

-- q ≥ 3 时 q·27 ≥ 81
81≤ : ∀ q → 81 ≤ suc (suc (suc q)) * 27
81≤ zero = ≤-refl
81≤ (suc q) = ≤-trans (81≤ q) (m≤n+m ((suc (suc (suc q))) * 27) 27)

-- q ≥ 4 时 q·27 ≥ 108
108≤ : ∀ q → 108 ≤ suc (suc (suc (suc q))) * 27
108≤ zero = ≤-refl
108≤ (suc q) = ≤-trans (108≤ q) (m≤n+m ((suc (suc (suc (suc q)))) * 27) 27)

--------------------------------------------------------------------------------
-- §2. 非根见证一：¬(27 ∣ 63)（x = 8 的 x² - 1 = 63 = 2·27 + 9）
--------------------------------------------------------------------------------

¬27∣63 : ¬ (27 ∣ 63)
¬27∣63 (divides zero h) =
  ≤<-asym 63 zero (subst (λ w → 63 ≤ w) h (≤-refl)) (s≤s z≤n)
¬27∣63 (divides (suc zero) h) =
  ≤<-asym 63 27 (subst (λ w → 63 ≤ w) h (≤-refl)) (1+<-trans 35 27)
¬27∣63 (divides (suc (suc zero)) h) =
  ≤<-asym 63 54 (subst (λ w → 63 ≤ w) h (≤-refl)) (1+<-trans 8 54)
¬27∣63 (divides (suc (suc (suc q))) h) =
  ≤<-asym 81 63
    (≤-trans (81≤ q) (subst (λ w → w ≤ 63) h (≤-refl)))
    (1+<-trans 17 63)

--------------------------------------------------------------------------------
-- §3. 非根见证二：¬(27 ∣ 99)（x = 10 的 x² - 1 = 99 = 3·27 + 18）
--------------------------------------------------------------------------------

¬27∣99 : ¬ (27 ∣ 99)
¬27∣99 (divides zero h) =
  ≤<-asym 99 zero (subst (λ w → 99 ≤ w) h (≤-refl)) (s≤s z≤n)
¬27∣99 (divides (suc zero) h) =
  ≤<-asym 99 27 (subst (λ w → 99 ≤ w) h (≤-refl)) (1+<-trans 71 27)
¬27∣99 (divides (suc (suc zero)) h) =
  ≤<-asym 99 54 (subst (λ w → 99 ≤ w) h (≤-refl)) (1+<-trans 44 54)
¬27∣99 (divides (suc (suc (suc zero))) h) =
  ≤<-asym 99 81 (subst (λ w → 99 ≤ w) h (≤-refl)) (1+<-trans 17 81)
¬27∣99 (divides (suc (suc (suc (suc q)))) h) =
  ≤<-asym 108 99
    (≤-trans (108≤ q) (subst (λ w → w ≤ 99) h (≤-refl)))
    (1+<-trans 8 99)
