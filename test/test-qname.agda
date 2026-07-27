{-# OPTIONS --cubical #-}
module test-qname where

import Cubical.Foundations.Prelude as C
open import Cubical.Foundations.Prelude using () renaming (_≡_ to _≡ᶜ_; refl to reflᶜ)

postulate A : Set ; x : A

-- Are these the same NAME?
open import Agda.Builtin.Bool

-- Just check if ≡ᶜ and C.≡ interoperate:
test-interop : (x ≡ᶜ x) → (x C.≡ x)
test-interop p = p

test-interop2 : (x C.≡ x) → (x ≡ᶜ x)
test-interop2 p = p
