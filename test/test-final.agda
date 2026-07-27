{-# OPTIONS --cubical #-}
module test-final where

import Cubical.Foundations.Prelude as C
import Relation.Binary.PropositionalEquality as P

postulate A : Set ; x : A

t1 t2 : Set
t1 = (x C.≡ x)   -- Cubical Prelude._≡_
t2 = (x P.≡ x)   -- PropEq._≡_ (= Agda.Builtin.Equality._≡_)

-- Are they definitionally equal?
test : t1 P.≡ t2
test = P.refl
