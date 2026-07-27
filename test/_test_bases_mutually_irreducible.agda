module _test_bases_mutually_irreducible where

open import Data.Nat using (ℕ; _<?_) ; open import Data.Nat.DivMod using (_%_)
open import Data.Nat.Properties using (m<n⇒m%n≡m)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

LCM : ℕ
LCM = 11609505792

-- 定理: ∀p < LCM, p % LCM = p, 因而 p % LCM ≠ 0
productIrreducible : (p : ℕ) → p < LCM → p % LCM ≡ 0 → ⊥
productIrreducible p p<LCM eq =
  let p%LCM≡p = m<n⇒m%n≡m p<LCM
      p≡0     = trans (sym p%LCM≡p) eq
  in refl p≡0
