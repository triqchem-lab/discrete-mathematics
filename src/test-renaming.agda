{-# OPTIONS --cubical #-}
module test-renaming where

open import Cubical.Foundations.Prelude using (refl)
open import Cubical.Foundations.Prelude using () renaming (_≡_ to _≡ᶜ_)
import Cubical.Foundations.Prelude as C

postulate A : Set ; x : A

t1 t2 : Set
t1 = (x C.≡ x)
t2 = (x ≡ᶜ x)

-- Are t1 and t2 definitionally equal under --cubical?
test : t1 C.≡ t2
test = refl
