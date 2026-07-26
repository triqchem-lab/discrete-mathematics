module refltest where
  open import Agda.Builtin.Nat using (Nat; zero; suc)
  open import Agda.Builtin.Equality using (_≡_; refl)
  test : ∀ n → suc n + 4 ≡ suc (n + 4)
  test n = refl
