{-# OPTIONS --rewriting --guardedness #-}
module _PCHK2 where
open import Data.Integer using (ℤ; _+_; +_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Sovereign.Algebra.LaurentCanon using (LaurentTerm; Laurent)
open import Sovereign.Algebra.LaurentSums using (sums)
chk-uncons : sums (+ 5 , + 0) ((+ 1 , + 0) ∷ ((+ 2 , + 1) ∷ []))
           ≡ sums (+ 5 , + 0) ((+ 1 , + 0) ∷ []) + sums (+ 5 , + 0) ((+ 2 , + 1) ∷ [])
chk-uncons = refl
