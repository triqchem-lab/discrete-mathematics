{-# OPTIONS --cubical #-}
module test-cubical-fix where

import Cubical.Foundations.Prelude as C
import Relation.Binary.PropositionalEquality as P

postulate A : Set ; x : A ; isSetA : C.isSet A
open import Cubical.Foundations.HLevels using (isOfHLevelPath)
open import Cubical.Foundations.Prelude using (isSet)

-- RED-LIGHT: isOfHLevelPath 2 isSetA x x : isSet (x P.≡ x)
test : isSet (x P.≡ x)
test = isOfHLevelPath 2 isSetA x x
