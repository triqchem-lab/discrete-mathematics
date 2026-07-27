{-# OPTIONS --cubical #-}
module test-iset-postulate where

open import Cubical.Foundations.Prelude using (isSet; _≡_)
open import Cubical.Foundations.HLevels using (isOfHLevelPath)

postulate A : Set
postulate isSetA : isSet A

test : (x : A) → isSet (x ≡ x)
test x = isOfHLevelPath 2 isSetA x x
