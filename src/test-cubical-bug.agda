{-# OPTIONS --cubical #-}
module test-cubical-bug where

import Cubical.Foundations.Prelude as C
import Relation.Binary.PropositionalEquality as P

postulate A : Set ; x : A ; isSetA : C.isSet A
open import Cubical.Foundations.HLevels using (isOfHLevelPath)
open import Cubical.Foundations.Prelude using (isSet)

-- The REAL test: isOfHLevelPath 2 isSetA x x should match
--     (a b : x P.≡ x) → (p q : a _≡_ b) → p _≡_ q
-- where _≡_ is PropEq
test-isOfHLevel : isSet (x P.≡ x)
test-isOfHLevel = isOfHLevelPath 2 isSetA x x
