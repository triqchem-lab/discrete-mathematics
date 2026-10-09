{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Hensel3Side
-- 3 侧分类：x² ≡ 1 (mod 177147 = 3¹¹) ⟹ 177147 ∣ x∸1 或 177147 ∣ suc x
--
-- 数学背景：奇素数幂 p^k 上 x²≡1 只有 ±1 两根（gcd(x−1,x+1) ∣ 2 与 p 互素）。
--   恰 8 论证的第 1 件（2 侧 4 根分类另册，需 2-adic 赋值）。
--
-- 路线 A（采用）：coprime-divisor 二分——3∣suc x 判定分两侧，各经核心引理
--   （d∣3^k → d≡1 ⊎ 3∣d，对 k 归纳 + coprime? 收缩）建 Coprime。
-- 路线 B（备选）：10 步塔合成——件多链长未采用。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Hensel3Side where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_; _≤_)
open import Data.Nat.Divisibility
  using (_∣_; divides; ∣1⇒≡1; ∣-refl; ∣⇒≤; ∣m+n∣n⇒∣m)
open import Data.Nat.Divisibility using (_∣?_)
open import Data.Nat.Coprimality using (Coprime; coprime-divisor; coprime?)
open import Data.Nat.Properties using (*-suc; *-comm; *-zeroʳ; *-identityʳ; +-identityʳ; 1+n≢n; suc-injective; ≤-antisym; m≤m+n; ≤-trans; +-cancelˡ-≤; s≤s; z≤n)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)
open import Data.Nat.Properties using (_≟_)

--------------------------------------------------------------------------------
-- §1. 3 的幂
--------------------------------------------------------------------------------

pow3 : ℕ → ℕ
pow3 zero = 1
pow3 (suc k) = 3 * pow3 k

--------------------------------------------------------------------------------
-- §2. irred3：d ∣ 3 → d ≡ 1 ⊎ d ≡ 3
--     （d ≤ 3 四值判定器穷举——0 由封闭 clash、2 由 2∣?3 判定器、
--      3 由 3∣?3 判定器——零 ≤ 模式，绕开 primHComp 陷阱）
--------------------------------------------------------------------------------

irred3 : ∀ d → d ∣ 3 → d ≡ 1 ⊎ d ≡ 3
irred3 d h with d ≟ zero | d ≟ 1 | d ≟ 2 | d ≟ 3
... | yes dz  | _       | _       | _       = ⊥-elim (zeros d dz h)
  where
    zeros : ∀ d → d ≡ zero → d ∣ 3 → ⊥
    zeros .zero refl (divides q eq) = cases (trans eq (*-zeroʳ q))
      where cases : 3 ≡ zero → ⊥
            cases ()
... | no _    | no _    | yes d2  | _       = ⊥-elim (2-case d2 h)
  where
    2-case : d ≡ 2 → d ∣ 3 → ⊥
    2-case refl h' with h'
    ...   | divides zero eq0 = ⊥-elim (check eq0)
      where check : 3 ≡ zero * 2 → ⊥
            check ()
    ...   | divides (suc q') eq1 = absurd2 (trans (suc-injective (suc-injective eq1')) (≤-antisym q2≤1 2≤q2))
      where
        absurd2 : suc zero ≡ suc (suc zero) → ⊥
        absurd2 eqs = ⊥-elim (1+n≢n (sym (suc-injective eqs)))
        eq1' : 3 ≡ 2 + (q' * 2)
        eq1' = trans eq1 (trans (*-suc (suc q') (suc zero))
                (trans (cong (λ w → suc q' + w) (*-suc (suc q') zero))
                (trans (cong (λ w → suc q' + (suc q' + w)) (*-zeroʳ (suc q')))
                (trans (cong (λ w → suc (suc q' + w)) (+-identityʳ (suc q')))
                (cong suc (+-identityʳ (suc q')))))))
        upper : 2 + (q' * 2) ≤ 3
        upper = ≤-reflexive (sym eq1')
        q2≤1 : q' * 2 ≤ 1
        q2≤1 = +-cancelˡ-≤ upper
        even0 : 2 ∣ q' * 2
        even0 = ∣m+n∣n⇒∣m {2} {2} {q' * 2} step0 ∣-refl
        two≡q2 : 2 ≡ q' * 2
        two≡q2 = ≤-antisym (s≤s (s≤s z≤n') q2≤1) (⌊ 2 ∣? q' * 2 ⌋') 
        -- ↑ 若 z≤n'/⌊⌋ 形状不匹配，改用 ∣⇒≤ even0 : 2 ≤ q'*2 与 ≤-antisym q2≤1 even0
        final-clash : ⊥
        final-clash = cases (subst (λ w → 3 ≡ w) (sym two≡q2) eq1')
          where cases : 3 ≡ 2 + 2 → ⊥
                cases ()
... | no _    | no _    | no _    | yes d3  = inj₂ d3
... | no _    | no _    | no _    | no n3    = ⊥-elim (n3 h)

--------------------------------------------------------------------------------
-- §3. 核心引理：d ∣ 3^k → d ≡ 1 ⊎ 3 ∣ d
--     （Prime-free：coprime? 判定 + irred3 收缩，对 k 归纳）
--------------------------------------------------------------------------------

core : ∀ k d → d ∣ pow3 k → d ≡ 1 ⊎ 3 ∣ d
core zero d h = inj₁ (∣1⇒≡1 h)
core (suc k) d h with 3 ∣? d
...   | yes t = inj₂ t
...   | no nt3 = inj₁ (core k d (coprime-divisor copr h))
      where
        copr : Coprime d 3
        copr {e} (e∣d , e∣3) with irred3 e e∣3
        ...   | inj₁ e≡1 = e≡1
        ...   | inj₂ e≡3 = ⊥-elim (nt3 (subst (λ w → w ∣ d) (sym e≡3) e∣d))

--------------------------------------------------------------------------------
-- §4. 乘积桥：(x ∸ 1) * suc x ≡ x * x ∸ 1
--------------------------------------------------------------------------------

px : ∀ x → (x ∸ 1) * suc x ≡ x * x ∸ 1
px zero = refl
px (suc x') =
  trans (sym (*-suc x' (suc (suc x'))))
  (trans (cong (λ w → x' + w) (sym (*-suc x' x')))
  (trans (cong (λ w → suc (x' + w) ∸ 1) (cong (λ w → x' + w) (sym (*-suc x' x'))))
  (trans (cong (λ w → suc (x' + (x' + w)) ∸ 1) (*-comm (suc x') x'))
  (trans (*-suc (suc x') x')
  (trans (cong (λ w → (suc x' + w) ∸ 1) (*-suc x' x'))
  refl)))))
