{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Cubical.Fin3 where

open import Cubical.Data.Fin.Base using (Fin; fzero; fsuc)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; _+_; _·_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm; ·DistR+)
open import Sovereign.Cubical.Fin3Sum9 using (sum9-swap)

assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)

sum3 : (Fin 3 → ℤ) → ℤ
sum3 f = f fzero + (f (fsuc fzero) + f (fsuc (fsuc fzero)))

sum3-cong : ∀ (f g : Fin 3 → ℤ) →
  f fzero ≡ g fzero → f (fsuc fzero) ≡ g (fsuc fzero) → f (fsuc (fsuc fzero)) ≡ g (fsuc (fsuc fzero)) →
  sum3 f ≡ sum3 g
sum3-cong f g p₀ p₁ p₂ = cong₂ _+_ p₀ (cong₂ _+_ p₁ p₂)

-- sum9-swap 由 Sovereign.Cubical.Fin3Sum9 提供（搬运方案：Fin3Sum9 环境已验证绿）

-- ─── sum3 交换与分配 ───

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
      ·DistR+ a (f fzero) ((f (fsuc fzero)) + (f (fsuc (fsuc fzero))))
  ∙ cong ((a · f fzero) +_) (·DistR+ a (f (fsuc fzero)) (f (fsuc (fsuc fzero))))