{-# OPTIONS --cubical #-}
module test-simple where

import Cubical.Foundations.Prelude as C
import Relation.Binary.PropositionalEquality as P

postulate A : Set ; x : A ; isSetA : C.isSet A
open import Cubical.Foundations.HLevels using (isOfHLevelPath)
open import Cubical.Foundations.Prelude using (isSet)

-- TEST: type compatibility — isSet (x C.≡ x) accepted where isSet (x P.≡ x) expected?
test : isSet (x P.≡ x)
test = isOfHLevelPath 2 isSetA x x
