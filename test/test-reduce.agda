{-# OPTIONS --cubical #-}
module test-reduce where

open import Cubical.Foundations.Prelude using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Check: are these definitionally equal under --cubical?
postulate A : Set
postulate x y : A

test : (x Cubical.Foundations.Prelude.≡ y) ≡ (x Relation.Binary.PropositionalEquality.≡ y)
test = {!!}
