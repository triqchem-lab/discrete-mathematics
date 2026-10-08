{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Cubical._ProbeSum3 where

open import Cubical.Data.Fin using (Fin; fzero; fsuc)
open import Cubical.Data.Int using (ℤ; _+_)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm)

+Assoc' : ∀ a b c → a + (b + c) ≡ (a + b) + c
+Assoc' = +Assoc

+Comm' : ∀ a b → a + b ≡ b + a
+Comm' = +Comm

+interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+interchange a b c d =
      sym (+Assoc a b (c + d))
  ∙ cong (a +_) (+Assoc b c d)
  ∙ cong (λ w → a + (w + d)) (+Comm b c)
  ∙ cong (a +_) (sym (+Assoc c b d))
  ∙ +Assoc a c (b + d)

sum3 : (Fin 3 → ℤ) → ℤ
sum3 f = f fzero + (f (fsuc fzero) + f (fsuc (fsuc fzero)))

sum3-comm : ∀ (f : Fin 3 → Fin 3 → ℤ) →
  sum3 (λ k → sum3 (λ l → f k l)) ≡ sum3 (λ l → sum3 (λ k → f k l))
sum3-comm f = ?
