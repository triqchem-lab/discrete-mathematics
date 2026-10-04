{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselLiftRoot1
-- 任务书第三层·3.2 收官：Hensel 提升**唯一性**实例（根 x ≡ 1 mod 3）
--
-- 数学背景：R12 的 HenselLiftUniqueness 闭合了根 x ≡ 2 的枚举。本模块
--   补全另一根 x ≡ 1 的三候选 x ∈ {1, 4, 7}：
--     x = 1：9∣0  —— 根（复用 R7 lift-1-mod-9）
--     x = 4：¬(9∣15) —— 非根
--     x = 7：¬(9∣48) —— 非根
--   与 R12 合并后，f(x) = x² - 1 的 mod 9 Hensel 全景（两根四非根）
--   全部机器闭合。
--
-- 复用：R12 的 ≤<-asym / 1+<-trans / 18≤suc2（严格 < 经 18 ≤ x ≡ 17 < x
--   定义性展开）；新递归引理 54≤suc6（q ≥ 6 时 q·9 ≥ 54，即 53 < q·9）。
--
-- ⚠ 诚实边界：同 R12（枚举见证针对具体候选；一般定理 roadmap）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselLiftRoot1 where

open import Data.Nat using (ℕ; zero; suc; _*_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Empty using (⊥)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.Properties
  using (≤-refl; ≤-antisym; ≤-trans; <-trans; <-irrefl; <⇒≤; m≤n+m)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Sovereign.Algebra.HenselLiftUniqueness
  using (≤<-asym; 1+<-trans; 18≤suc2)
open import Sovereign.Algebra.HenselLiftMinimal using (lift-1-mod-9)

--------------------------------------------------------------------------------
-- §1. 递归引理：q ≥ 6 时 q·9 ≥ 54（即 53 < q·9）
--------------------------------------------------------------------------------

54≤suc6 : ∀ q → 54 ≤ suc (suc (suc (suc (suc (suc q))))) * 9
54≤suc6 zero = ≤-refl
54≤suc6 (suc q) =
  ≤-trans (54≤suc6 q)
          (m≤n+m ((suc (suc (suc (suc (suc (suc q)))))) * 9) 9)

-- 定义性展开：54 ≤ x 即 53 < x
53<q*9 : ∀ q → 53 < suc (suc (suc (suc (suc (suc q))))) * 9
53<q*9 q = 54≤suc6 q

--------------------------------------------------------------------------------
-- §2. 非根见证一：¬(9 ∣ 15)（x = 4 的 x² - 1 = 15 不是 mod 9 的零）
--------------------------------------------------------------------------------

¬9∣15 : ¬ (9 ∣ 15)
¬9∣15 (divides zero h) =
  ≤<-asym 15 zero (subst (λ w → 15 ≤ w) h (≤-refl)) (s≤s z≤n)
¬9∣15 (divides (suc zero) h) =
  ≤<-asym 15 9 (subst (λ w → 15 ≤ w) h (≤-refl)) (1+<-trans 5 9)
¬9∣15 (divides (suc (suc q'')) h) =
  ≤<-asym ((suc (suc q'')) * 9) 15
    (subst (λ w → w ≤ 15) h (≤-refl))
    (<-trans (1+<-trans 1 15) (18≤suc2 q''))

--------------------------------------------------------------------------------
-- §3. 非根见证二：¬(9 ∣ 48)（x = 7 的 x² - 1 = 48 不是 mod 9 的零）
--------------------------------------------------------------------------------

¬9∣48 : ¬ (9 ∣ 48)
¬9∣48 (divides zero h) =
  ≤<-asym 48 zero (subst (λ w → 48 ≤ w) h (≤-refl)) (s≤s z≤n)
¬9∣48 (divides (suc zero) h) =
  ≤<-asym 48 9 (subst (λ w → 48 ≤ w) h (≤-refl)) (1+<-trans 38 9)
¬9∣48 (divides (suc (suc zero)) h) =
  ≤<-asym 48 18 (subst (λ w → 48 ≤ w) h (≤-refl)) (1+<-trans 29 18)
¬9∣48 (divides (suc (suc (suc zero))) h) =
  ≤<-asym 48 27 (subst (λ w → 48 ≤ w) h (≤-refl)) (1+<-trans 20 27)
¬9∣48 (divides (suc (suc (suc (suc zero)))) h) =
  ≤<-asym 48 36 (subst (λ w → 48 ≤ w) h (≤-refl)) (1+<-trans 11 36)
¬9∣48 (divides (suc (suc (suc (suc (suc zero))))) h) =
  ≤<-asym 48 45 (subst (λ w → 48 ≤ w) h (≤-refl)) (1+<-trans 2 45)
¬9∣48 (divides (suc (suc (suc (suc (suc (suc q)))))) h) =
  ≤<-asym ((suc (suc (suc (suc (suc (suc q)))))) * 9) 48
    (subst (λ w → w ≤ 48) h (≤-refl))
    (<-trans (1+<-trans 4 48) (53<q*9 q))

--------------------------------------------------------------------------------
-- §4. 根 x ≡ 1 (mod 3) 的提升枚举
--
--   x = 1：9∣0  —— 根（R7 lift-1-mod-9）
--   x = 4：¬(9∣15) —— 非根（§2）
--   x = 7：¬(9∣48) —— 非根（§3）
--------------------------------------------------------------------------------

lift-witness-1 : 9 ∣ ((1 * 1) ∸ 1)
lift-witness-1 = lift-1-mod-9
