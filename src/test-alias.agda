{-# OPTIONS --cubical #-}
module test-alias where

import Cubical.Foundations.Prelude as C
open import Cubical.Foundations.Prelude using () renaming (_≡_ to _≡ᶜ_; refl to reflᶜ)
open import Relation.Binary.PropositionalEquality using (_≡_)

postulate A : Set ; x : A

-- Test: does ≡ᶜ and C.≡ match definitionally?
test : (x ≡ᶜ x) ≡ (x C.≡ x)
test = reflᶜ
