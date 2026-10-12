{-# OPTIONS --guardedness #-}
module ProbeI where

open import Data.Nat.Base using (ℕ)
open import Data.Integer using (ℤ; _+_; 0ℤ)
open import Data.Integer.Properties using (+-*-commutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Tactic.RingSolver.NonReflective as NR
open import Tactic.RingSolver.Core.AlmostCommutativeRing using (AlmostCommutativeRing)

ring : AlmostCommutativeRing _ _
ring = +-*-commutativeRing
open NR ring public

-- NonReflective：solve 显式传变量向量（无 reflection macro）
test : ∀ a b c d e f →
  (a ⊕ (b ⊕ c)) ⊕ ((d ⊕ (e ⊕ f)) ⊕ (0ℤ)) ≡
  ((a ⊕ (d ⊕ 0ℤ)) ⊕ ((b ⊕ (e ⊕ 0ℤ)) ⊕ (c ⊕ (f ⊕ 0ℤ))))
test = solve 6 λ a b c d e f → Κ (a ⊕ (b ⊕ c)) + Κ ((d ⊕ (e ⊕ f)) ⊕ Κ 0ℤ) ≈ (a + (d + Κ 0ℤ)) + ((b + (e + Κ 0ℤ)) + (c + (f + Κ 0ℤ)))
