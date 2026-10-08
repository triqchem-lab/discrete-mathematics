{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Algebra._ProbeAssoc where

open import Cubical.Data.Int using (ℤ; _+_; _·_)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm; ·DistR+; ·DistL+; ·Assoc)

-- gather：提取公因子 a
gather : ∀ a x y z → ((a · x) + (a · y)) + (a · z) ≡ a · ((x + y) + z)
gather a x y z = sym (cong (a ·_) (+Assoc x y z)) ∙ symInner
  where
    symInner : ((a · x) + (a · y)) + (a · z) ≡ (a · (x + y)) + (a · z)
gather a x y z =
      sym (+Assoc (a · x) (a · y) (a · z))
  ∙ cong (λ w → (a · x) + w) (sym (·DistR+ a y z))
target : ∀ (a₁ a₂ a₃ b11 b12 b13 b21 b22 b23 b31 b32 b33 c1 c2 c3 : ℤ) →
  ((((a₁ · (b11 · c1)) + (a₂ · (b21 · c1))) + (a₃ · (b31 · c1))) + (((a₁ · (b12 · c2)) + (a₂ · (b22 · c2))) + (a₃ · (b32 · c2)))) + (((a₁ · (b13 · c3)) + (a₂ · (b23 · c3))) + (a₃ · (b33 · c3))) ≡ ((a₁ · (((b11 · c1) + (b12 · c2)) + (b13 · c3))) + (a₂ · (((b21 · c1) + (b22 · c2)) + (b23 · c3)))) + (a₃ · (((b31 · c1) + (b32 · c2)) + (b33 · c3)))))
target a₁ a₂ a₃ b11 b12 b13 b21 b22 b23 b31 b32 b33 c1 c2 c3 = ?