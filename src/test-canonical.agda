{-# OPTIONS --cubical #-}
module test-canonical where

import Cubical.Foundations.Prelude as C
import Relation.Binary.PropositionalEquality as P
open import Cubical.Data.Equality.Conversion using (pathToEq; eqToPath)

postulate A : Set ; x y : A

test1 : (x C.≡ y) → (x P.≡ y)
test1 p = pathToEq p

test2 : (x P.≡ y) → (x C.≡ y)
test2 p = eqToPath p

-- Direct type equality test:
-- Does Agda recognize that (x C.≡ y) and (x P.≡ y) are the same type?
test3 : (x C.≡ y) P.≡ (x P.≡ y)
test3 = pathToEq C.refl
