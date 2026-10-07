{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Cubical.Fin3 where

open import Cubical.Data.Fin.Base using (Fin; fzero; fsuc)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; _+_; _·_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm; ·DistR+)

assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)

sum3 : (Fin 3 → ℤ) → ℤ
sum3 f = f fzero + (f (fsuc fzero) + f (fsuc (fsuc fzero)))

sum3-cong : ∀ (f g : Fin 3 → ℤ) →
  f fzero ≡ g fzero → f (fsuc fzero) ≡ g (fsuc fzero) → f (fsuc (fsuc fzero)) ≡ g (fsuc (fsuc fzero)) →
  sum3 f ≡ sum3 g
sum3-cong f g p₀ p₁ p₂ = cong₂ _+_ p₀ (cong₂ _+_ p₁ p₂)

-- ────────────────────────────────────────────────────────────────────
-- 分段签名引理（test5 模式：每段独立正向类型检查，绕开 ∙ 链中段 stuck 统一）
-- ────────────────────────────────────────────────────────────────────

-- 段1：组形 → 全右结合 9 叶（flatten，assocP 正向 4 步）
unflat9 : ∀ A1 A2 A3 B1 B2 B3 C1 C2 C3 →
      A1 + (B1 + (C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
  ≡   (A1 + (B1 + C1)) + ((A2 + (B2 + C2)) + (A3 + (B3 + C3)))
unflat9 A1 A2 A3 B1 B2 B3 C1 C2 C3 =
      assocP A1 B1 (C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3))))))
  ∙ assocP (A1 + B1) C1 (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))
  ∙ cong (λ w1 → ((A1 + B1) + C1) + w1) (assocP A2 B2 (C2 + (A3 + (B3 + C3))))
  ∙ cong (λ w1 → ((A1 + B1) + C1) + w1) (assocP (A2 + B2) C2 (A3 + (B3 + C3)))
  ∙ cong (λ w2 → ((A1 + B1) + C1) + ((w2 + (A3 + (B3 + C3))))) (sym (assocP A2 B2 C2))
  ∙ cong (λ w → w + ((A2 + (B2 + C2)) + (A3 + (B3 + C3)))) (sym (assocP A1 B1 C1))

flat9 : ∀ A1 A2 A3 B1 B2 B3 C1 C2 C3 →
      (A1 + (A2 + A3)) + ((B1 + (B2 + B3)) + (C1 + (C2 + C3)))
  ≡   A1 + (A2 + (((A3 + (B1 + (B2 + B3))) + (C1 + (C2 + C3)))))
flat9 A1 A2 A3 B1 B2 B3 C1 C2 C3 =
      assocP A1 (A2 + A3) ((B1 + (B2 + B3)) + (C1 + (C2 + C3)))
  ∙ cong (A1 +_) (assocP A2 A3 ((B1 + (B2 + B3)) + (C1 + (C2 + C3))))
  ∙ cong (A1 +_) (cong (A2 +_) (assocP A3 (B1 + (B2 + B3)) (C1 + (C2 + C3))))

swap9 : ∀ A1 A2 A3 B1 B2 B3 C1 C2 C3 →
      A1 + (A2 + (((A3 + (B1 + (B2 + B3))) + (C1 + (C2 + C3)))))
  ≡   A1 + (B1 + (C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
swap9 A1 A2 A3 B1 B2 B3 C1 C2 C3 = {!!}
sum9-swap : ∀ A1 A2 A3 B1 B2 B3 C1 C2 C3 →
      (A1 + (A2 + A3)) + ((B1 + (B2 + B3)) + (C1 + (C2 + C3)))
  ≡   (A1 + (B1 + C1)) + ((A2 + (B2 + C2)) + (A3 + (B3 + C3)))
sum9-swap A1 A2 A3 B1 B2 B3 C1 C2 C3 =
  flat9 A1 A2 A3 B1 B2 B3 C1 C2 C3
  ∙ swap9 A1 A2 A3 B1 B2 B3 C1 C2 C3
  ∙ unflat9 A1 A2 A3 B1 B2 B3 C1 C2 C3


sum3-comm : ∀ (f : Fin 3 → Fin 3 → ℤ) →
  sum3 (λ k → sum3 (λ l → f k l)) ≡ sum3 (λ l → sum3 (λ k → f k l))
sum3-comm f =
  sum9-swap
    (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero)))
    (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero)))
    (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero)))

sum3-distribˡ : ∀ (a : ℤ) (f : Fin 3 → ℤ) →
  a · sum3 f ≡ sum3 (λ k → a · f k)
sum3-distribˡ a f =
      cong₂ _+_ (·DistR+ a (f fzero) (f (fsuc fzero) + f (fsuc (fsuc fzero)))) refl
  ∙ cong (λ w → (a · f fzero) + w) (cong₂ _+_ (·DistR+ a (f (fsuc fzero)) (f (fsuc (fsuc fzero)))) refl)
