{-# OPTIONS --rewriting --guardedness #-}
module _PCHK where
open import Data.Integer using (ℤ; _+_; +_; _≟_)

open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Data.List using (List; []; _∷_)
open import Sovereign.Algebra.LaurentCanon using (LaurentTerm; Laurent; Canon; canon-one)
open import Sovereign.Algebra.LaurentNorm using (insertCᵌ)
open import Sovereign.Algebra.LaurentSums using (sums; sums-uncons)
chk-insert : proj₁ (insertCᵌ (+ 3 , + 0) ((+ 1 , + 1) ∷ []) (canon-one (+ 1 , + 1)))
           ≡ (+ 1 , + 1) ∷ ((+ 3 , + 0) ∷ [])
chk-insert = refl
