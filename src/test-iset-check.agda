{-# OPTIONS --cubical #-}
module test-iset-check where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

postulate A : Set
postulate isSetA : isSet A

-- isSetA : (x y : A) → isProp (x ≡ y)
-- isSetA x x : isProp (x ≡ x) = (p q : x ≡ x) → p ≡ q

-- isPropIsSet : isProp (isSet A) = (f g : isSet A) → f ≡ g
-- isPropIsSet {e} : (f g : isSet e) → f ≡ g

-- test expects: isSet (x ≡ x) = (p q : x ≡ x) → isProp (p ≡ q)

-- The issue: isPropIsSet returns isProp (isSet e), not isSet e
-- test needs isSet (x ≡ x), which needs 2 more arguments

-- Correct usage:
test : (x : A) → isProp (isSet (x ≡ x))
test x = isPropIsSet
