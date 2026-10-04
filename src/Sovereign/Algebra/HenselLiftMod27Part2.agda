{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselLiftMod27Part2
-- 任务书第三层·3.2 深化：mod 27 唯一性 part 2——¬(27 ∣ 288)
--
-- 数学背景：x = 17 的 x² - 1 = 288 = 10·27 + 18 → x = 17 不是 mod 27 根。
--   这是 mod 9 根 x ≡ 8 的提升候选 x ∈ {8, 17, 26} 的排除枚举第二件
--   （x = 8 已由 ¬(27∣63) 排除，x = 26 正见证在 Tower）。
--
-- 技术要点：q ≥ 11 分支的下界引理 289≤suc11（base 经 ≤-trans ≤-refl
--   m≤m+n 闭合——≤-refl 对封闭项无深分裂陷阱），289 ≤ x 经定义性展开
--   即 288 < x。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselLiftMod27Part2 where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Empty using (⊥)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; m≤m+n; m≤n+m; <-trans)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)
open import Sovereign.Algebra.HenselLiftUniqueness using (≤<-asym; 1+<-trans)

--------------------------------------------------------------------------------
-- §1. 递归下界引理：q ≥ 11 时 q·27 ≥ 289（即 288 < q·27）
--------------------------------------------------------------------------------

289≤suc11 : ∀ q → 289 ≤ (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (q)))))))))))) * 27
289≤suc11 zero = ≤-trans (≤-refl {289}) (m≤m+n 289 8)
289≤suc11 (suc q) =
  ≤-trans (289≤suc11 q)
          (m≤n+m (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc q)))))))))))) * 27) 27)

--------------------------------------------------------------------------------
-- §2. 非根见证：¬(27 ∣ 288)
--
-- q = 0..10 具体分支：288 ≤ q·27（subst）+ q·27 < 288（1+<-trans 链，
--   k = 287 - 27q）；q ≥ 11：289 ≤ q·27（递归引理，定义性给出 288 < q·27）
--   与 q·27 ≤ 288（subst）汇入 ≤<-asym。
--------------------------------------------------------------------------------

¬27∣288 : ¬ (27 ∣ 288)
¬27∣288 (divides zero h) =
  ≤<-asym 288 zero (subst (λ w → 288 ≤ w) h (≤-refl)) (s≤s z≤n)
¬27∣288 (divides (suc zero) h) =
  ≤<-asym 288 27 (subst (λ w → 288 ≤ w) h (≤-refl)) (1+<-trans 260 27)
¬27∣288 (divides (suc (suc zero)) h) =
  ≤<-asym 288 54 (subst (λ w → 288 ≤ w) h (≤-refl)) (1+<-trans 233 54)
¬27∣288 (divides (suc (suc (suc zero))) h) =
  ≤<-asym 288 81 (subst (λ w → 288 ≤ w) h (≤-refl)) (1+<-trans 206 81)
¬27∣288 (divides (suc (suc (suc (suc zero)))) h) =
  ≤<-asym 288 108 (subst (λ w → 288 ≤ w) h (≤-refl)) (1+<-trans 179 108)
¬27∣288 (divides (suc (suc (suc (suc (suc zero))))) h) =
  ≤<-asym 288 135 (subst (λ w → 288 ≤ w) h (≤-refl)) (1+<-trans 152 135)
¬27∣288 (divides (suc (suc (suc (suc (suc (suc zero))))))) h) =
  ≤<-asym 288 162 (subst (λ w → 288 ≤ w) h (≤-refl)) (1+<-trans 125 162)
¬27∣288 (divides (suc (suc (suc (suc (suc (suc (suc zero)))))))) h) =
  ≤<-asym 288 189 (subst (λ w → 288 ≤ w) h (≤-refl)) (1+<-trans 98 189)
¬27∣288 (divides (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) h) =
  ≤<-asym 288 216 (subst (λ w → 288 ≤ w) h (≤-refl)) (1+<-trans 71 216)
¬27∣288 (divides (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) h) =
  ≤<-asym 288 243 (subst (λ w → 288 ≤ w) h (≤-refl)) (1+<-trans 44 243)
¬27∣288 (divides (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) h) =
  ≤<-asym 288 270 (subst (λ w → 288 ≤ w) h (≤-refl)) (1+<-trans 17 270)
¬27∣288 (divides (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (q)))))))))))) h) =
  ≤<-asym ((suc^11 q) * 27) 288
    (subst (λ w → w ≤ 288) h (≤-refl))
    (<-trans (1+<-trans 8 288) (289≤suc11 q))
  where
    suc^11 : ℕ → ℕ
    suc^11 n = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))))
