{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselLiftUniqueness
-- 任务书第三层·3.2 深化：Hensel 提升**唯一性**实例（根 x ≡ 2 mod 3）
--
-- 数学背景：R7 的 HenselLiftMinimal 闭合了提升**存在性**（x=8: 9∣63）。
--   本模块闭合根 x ≡ 2 (mod 3) 的三个候选提升 x ∈ {2, 5, 8} 的**排除
--   枚举**：x=2 与 x=5 不是 mod 9 根（¬(9∣3)、¬(9∣24)），唯 x=8 是
--   （9∣63，复用 R7）——「唯一性」在该实例上的显式枚举见证。
--
-- 技术要点：矛盾统一经 ≤<-asym（a ≤ b ∧ b < a → ⊥）导出；严格 < 的
--   来源 = 整除引理的**定义性展开**（27 ≤ x ≡ 26 < x，18 ≤ x ≡ 17 < x，
--   m < n ≡ suc m ≤ n）。
--
-- ⚠ 诚实边界：枚举见证针对三个具体候选；一般 Hensel 唯一性
--   （∀x 量化 + f'(a) 条件的形式化）roadmap。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselLiftUniqueness where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.Properties
  using (≤-refl; ≤-antisym; ≤-trans; <-trans; <-irrefl; <⇒≤; m≤m+n; m≤n+m;
         n<1+n)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

--------------------------------------------------------------------------------
-- §1. 泛型助手
--------------------------------------------------------------------------------

-- ≤ 与 < 的不对称：a ≤ b 且 b < a 不可能（经 ≤-antisym 归约到 <-irrefl）
≤<-asym : ∀ a b → a ≤ b → b < a → ⊥
≤<-asym a b a≤b b<a =
  <-irrefl refl (subst (λ w → b < w) (≤-antisym a≤b (<⇒≤ b<a)) b<a)

-- 链式 < ：n < suc (k + n)（suc k + n ≡ suc (k + n) 定义性成立）
1+<-trans : ∀ k n → n < suc (k + n)
1+<-trans zero n = n<1+n n
1+<-trans (suc k) n = <-trans (1+<-trans k n) (s≤s (n<1+n (k + n)))

--------------------------------------------------------------------------------
-- §2. 非根见证一：¬(9 ∣ 3)（x = 2 的 x² - 1 = 3 不是 mod 9 的零）
--------------------------------------------------------------------------------

-- 递归引理：q ≥ 2 时 q·9 ≥ 18（即 17 < q·9）
18≤suc2 : ∀ q'' → 18 ≤ suc (suc q'') * 9
18≤suc2 zero = ≤-refl
18≤suc2 (suc q'') = ≤-trans (18≤suc2 q'') (m≤n+m (suc (suc q'') * 9) 9)

¬9∣3 : ¬ (9 ∣ 3)
¬9∣3 (divides zero h) =
  ≤<-asym 3 zero (subst (λ w → 3 ≤ w) h (≤-refl)) (s≤s z≤n)
¬9∣3 (divides (suc zero) h) =
  ≤<-asym 9 3 (subst (λ w → 9 ≤ w) (sym h) (≤-refl)) (1+<-trans 5 3)
¬9∣3 (divides (suc (suc q'')) h) =
  ≤<-asym ((suc (suc q'')) * 9) 3
    (subst (λ w → w ≤ 3) h (≤-refl))
    (<-trans (1+<-trans 13 3) (18≤suc2 q''))

--------------------------------------------------------------------------------
-- §3. 非根见证二：¬(9 ∣ 24)（x = 5 的 x² - 1 = 24 不是 mod 9 的零）
--------------------------------------------------------------------------------

-- 递归引理：q ≥ 3 时 q·9 ≥ 27（即 26 < q·9）
27≤ : ∀ q → 27 ≤ suc (suc (suc q)) * 9
27≤ zero = ≤-refl
27≤ (suc q) = ≤-trans (27≤ q) (m≤n+m (suc (suc (suc q)) * 9) 9)

¬9∣24 : ¬ (9 ∣ 24)
¬9∣24 (divides zero h) =
  ≤<-asym 24 zero (subst (λ w → 24 ≤ w) h (≤-refl)) (s≤s z≤n)
¬9∣24 (divides (suc zero) h) =
  ≤<-asym 24 9 (subst (λ w → 24 ≤ w) h (≤-refl)) (1+<-trans 14 9)
¬9∣24 (divides (suc (suc zero)) h) =
  ≤<-asym 24 18 (subst (λ w → 24 ≤ w) h (≤-refl)) (1+<-trans 5 18)
¬9∣24 (divides (suc (suc (suc q'))) h) =
  ≤<-asym ((suc (suc (suc q'))) * 9) 24
    (subst (λ w → w ≤ 24) h (≤-refl))
    (<-trans (1+<-trans 1 24) (27≤ q'))

--------------------------------------------------------------------------------
-- §4. 根 x ≡ 2 (mod 3) 的提升枚举（唯一性的显式见证）
--
--   x = 2：¬(9∣3)  —— 非根（§2）
--   x = 5：¬(9∣24) —— 非根（§3）
--   x = 8：9∣63    —— 根（复用 HenselLiftMinimal.lift-8-mod-9）
--
--   三个候选中恰一个提升成功——唯一性在该实例上的枚举见证。
--------------------------------------------------------------------------------

import Sovereign.Algebra.HenselLiftMinimal as HLM

lift-witness-8 : 9 ∣ ((8 * 8) ∸ 1)
lift-witness-8 = HLM.lift-8-mod-9
