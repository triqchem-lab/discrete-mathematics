{-# OPTIONS --rewriting --cubical --guardedness #-}

-- | Sovereign.Projection.Decimal.Proofs
-- 十进制数字根正确性的构造性证明
--
-- ⚠️ 宪法声明：
-- - 这些证明在十进制自然数体系内**严谨完备**
-- - 但与律算 GF(3) 驻波叠加表属于**不同范畴**
-- - 证明内容包括：
--   1. divMod10Correct：十进制除法正确性
--   2. sumDigitsTerminates：数字和递归终止性
--   3. digitalRoot 稳定性证明
--
-- 2026-08 P0 收口 (路线 a): 全部 0 postulate —
--   Axioms.divMod10 已改为 stdlib 对齐的 with-free 定义 (n/10, n%10),
--   sumDigits 同改; 正确性由 m≡m%n+[m/n]*n + m%n<n + m/n<m 直证,
--   终止性/稳定性由 <-wellFounded 良基归纳证明, 全程无 with。

module Sovereign.Projection.Decimal.Proofs where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _/_; _≤_; _≥_; _>_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (*-suc; +-comm; +-assoc; m<m+n; ≤-trans; ≤-refl; ≤-reflexive; m≤m+n; +-monoˡ-<; +-monoˡ-≤; +-monoʳ-≤; +-identityʳ; m≤n⇒m<n∨m≡n; ≤-pred; <⇒≤; 1+n≰n; ≤-<-trans)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n; m%n<n; m/n<m)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)

-- stdlib 2.4 未导出 ¬suc≤zero, 本地定义
¬suc≤zero : ∀ {n} → suc n ≤ zero → ⊥
¬suc≤zero ()

open import Sovereign.Projection.Decimal.Axioms

true≢false : true ≡ false → ⊥
true≢false ()

--------------------------------------------------------------------------------
-- 1. divMod10 正确性证明 (路线 a: stdlib 引理直证, 无 with)
--------------------------------------------------------------------------------

-- 辅助引理：乘法分配律 (2026-08 P0: 原 postulate → stdlib *-suc + +-comm)
suc-*-distrib : (q n : ℕ) → q * suc n ≡ q * n + q
suc-*-distrib q n = trans (*-suc q n) (+-comm q (q * n))

-- 定理：divMod10 n = (q, r) 满足 n = q * 10 + r 且 r < 10
divMod10Correct : (n : ℕ) →
  let (q , r) = divMod10 n
  in n ≡ q * 10 + r × r < 10
divMod10Correct n = (n≡ , m%n<n n 10)
  where
    n≡ : n ≡ (n / 10) * 10 + n % 10
    n≡ = trans (m≡m%n+[m/n]*n n 10) (+-comm (n % 10) ((n / 10) * 10))

--------------------------------------------------------------------------------
-- 2. sumDigits 终止性证明 (良基归纳, 无 with)
--------------------------------------------------------------------------------

-- 辅助引理：q ≥ 1 → q < q * 10 + r
lemma_q_lt : (q r : ℕ) → q ≥ 1 → q < q * 10 + r
lemma_q_lt q r q≥1 =
  subst (q <_) (lemma-q-eq q r) (m<m+n q {q * 9 + r} (nz q r q≥1))
  where
    lemma-q-eq : ∀ q r → q + (q * 9 + r) ≡ q * 10 + r
    lemma-q-eq q r =
      trans (sym (+-assoc q (q * 9) r)) (cong (_+ r) (sym (*-suc q 9)))
    nz : ∀ q r → q ≥ 1 → q * 9 + r > 0
    nz q r q≥1 =
      ≤-trans (≤-trans q≥1 (subst (λ x → q ≤ x) (sym (*-suc q 8)) (m≤m+n q (q * 8))))
        (m≤m+n (q * 9) r)

-- 辅助引理: q ≥ 1 → r < 10 → r + q < q * 10 + r
lemma_sum_lt : (q r : ℕ) → q ≥ 1 → r < 10 → r + q < q * 10 + r
lemma_sum_lt q r q≥1 r<10 =
  subst (λ x → x < q * 10 + r) (sym (+-comm r q))
    (subst (λ x → q + r < x + r) (+-identityʳ (q * 10))
      (+-monoˡ-< r (lemma_q_lt q 0 q≥1)))

q≤q*10 : ∀ q → q ≤ q * 10
q≤q*10 q = subst (λ x → q ≤ x) (sym (*-suc q 9)) (m≤m+n q (q * 9))

1<10 : 1 < 10
1<10 = s≤s (s≤s z≤n)

-- sumDigits n ≤ n (对全部 n)
sumDigitsBound : (n : ℕ) → sumDigits n ≤ n
sumDigitsBound n = go _ (<-wellFounded n)
  where
    go : ∀ n → Acc _<_ n → sumDigits n ≤ n
    go zero _ = z≤n
    go (suc n) (acc rec) =
      ≤-trans
        (+-monoʳ-≤ (suc n % 10) (go ((suc n) / 10) (rec (m/n<m (suc n) 10 1<10))))
        (≤-trans (+-monoʳ-≤ (suc n % 10) (q≤q*10 ((suc n) / 10)))
          (≤-reflexive (sym (m≡m%n+[m/n]*n (suc n) 10))))

suc-eq : ∀ m → (m / 10) * 10 + m % 10 ≡ m
suc-eq m = trans (+-comm ((m / 10) * 10) (m % 10)) (sym (m≡m%n+[m/n]*n m 10))

q≥1 : ∀ m → m ≥ 10 → m / 10 ≥ 1
q≥1 m m≥10 = f (m≤n⇒m<n∨m≡n z≤n)
  where
    f : 0 < m / 10 ⊎ 0 ≡ m / 10 → m / 10 ≥ 1
    f (inj₁ q>0) = q>0
    f (inj₂ q≡0) =
      ⊥-elim (1+n≰n (≤-trans m≥10 m≤9))
      where
        m≡r : m ≡ m % 10
        m≡r = trans (subst (λ q → m ≡ m % 10 + q * 10) (sym q≡0) (m≡m%n+[m/n]*n m 10))
          (+-identityʳ (m % 10))
        m≤9 : m ≤ 9
        m≤9 = ≤-pred (subst (λ x → x < 10) (sym m≡r) (m%n<n m 10))

-- 主定理：∀ n → n ≥ 10 → sumDigits n < n
sumDigitsTerminates : (n : ℕ) → n ≥ 10 → sumDigits n < n
sumDigitsTerminates n n≥10 = go _ (<-wellFounded n) n≥10
  where
    go : ∀ n → Acc _<_ n → n ≥ 10 → sumDigits n < n
    go zero _ n≥10 = ⊥-elim (1+n≰n (≤-trans n≥10 z≤n))
    go (suc n) (acc rec) n≥10 =
      subst (λ x → sumDigits (suc n) < x) (suc-eq (suc n))
        (≤-<-trans (+-monoʳ-≤ (suc n % 10) (sumDigitsBound ((suc n) / 10)))
          (lemma_sum_lt ((suc n) / 10) (suc n % 10) (q≥1 (suc n) n≥10) (m%n<n (suc n) 10)))

--------------------------------------------------------------------------------
-- 3. digitalRoot 收敛性与稳定性 (良基归纳, 无 with)
--------------------------------------------------------------------------------

digitalRootConverges : (n : ℕ) → digitalRoot n < 10
digitalRootConverges n = go _ (<-wellFounded n)
  where
    go : ∀ n → Acc _<_ n → digitalRoot n < 10
    go zero _ = s≤s z≤n
    go (suc zero) _ = s≤s (s≤s z≤n)
    go (suc (suc zero)) _ = s≤s (s≤s (s≤s z≤n))
    go (suc (suc (suc zero))) _ = s≤s (s≤s (s≤s (s≤s z≤n)))
    go (suc (suc (suc (suc zero)))) _ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
    go (suc (suc (suc (suc (suc zero))))) _ = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
    go (suc (suc (suc (suc (suc (suc zero)))))) _ = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
    go (suc (suc (suc (suc (suc (suc (suc zero))))))) _ = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
    go (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) _ = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    go (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) _ = s≤s ≤-refl
    go (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))) (acc rec) =
      go (sumDigits (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))
        (rec (sumDigitsTerminates (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))) n≥10))
      where
        n≥10 : suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))) ≥ 10
        n≥10 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

digitalRootStable : (n : ℕ) → IsStable n ≡ true →
  digitalRoot n ≡ 3 ⊎ digitalRoot n ≡ 6 ⊎ digitalRoot n ≡ 9
digitalRootStable n prem = go _ (<-wellFounded n) prem
  where
    go : ∀ n → Acc _<_ n → IsStable n ≡ true →
      digitalRoot n ≡ 3 ⊎ digitalRoot n ≡ 6 ⊎ digitalRoot n ≡ 9
    go zero _ prem = ⊥-elim (true≢false (sym prem))
    go (suc zero) _ prem = ⊥-elim (true≢false (sym prem))
    go (suc (suc zero)) _ prem = ⊥-elim (true≢false (sym prem))
    go (suc (suc (suc zero))) _ prem = inj₁ refl
    go (suc (suc (suc (suc zero)))) _ prem = ⊥-elim (true≢false (sym prem))
    go (suc (suc (suc (suc (suc zero))))) _ prem = ⊥-elim (true≢false (sym prem))
    go (suc (suc (suc (suc (suc (suc zero)))))) _ prem = inj₂ (inj₁ refl)
    go (suc (suc (suc (suc (suc (suc (suc zero))))))) _ prem = ⊥-elim (true≢false (sym prem))
    go (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) _ prem = ⊥-elim (true≢false (sym prem))
    go (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) _ prem = inj₂ (inj₂ refl)
    go (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))) (acc rec) prem =
      go (sumDigits (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))
        (rec (sumDigitsTerminates (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))) n≥10))
        prem
      where
        n≥10 : suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))) ≥ 10
        n≥10 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))
