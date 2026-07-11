{-# OPTIONS --cubical #-}
module test-trace where

import Cubical.Foundations.Prelude as C
import Relation.Binary.PropositionalEquality as P

postulate A : Set ; x : A ; isSetA : C.isSet A
open import Cubical.Foundations.HLevels using (isOfHLevelPath)
open import Cubical.Foundations.Prelude using (isSet)

-- Trace 1: direct type comparison
_ : C.isSet (x C.≡ x)
_ = isSetA

-- Trace 2: isOfHLevelPath into PropEq type
_ : isSet (x P.≡ x)
_ = isOfHLevelPath 2 isSetA x x

-- Trace 3: PropEq domain in Pi
postulate
  use-isSet : isSet (x P.≡ x) → Set
  provide-isSet : isSet (x P.≡ x)
