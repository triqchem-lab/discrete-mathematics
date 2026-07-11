{-# OPTIONS --guardedness #-}

module Sovereign.AlgebraWrapper where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Data.Nat.Properties using (0∸n≡0)

cancel : (a b c : ℕ) → (a + b) ∸ (a + c) ≡ b ∸ c
cancel zero    b c = refl
cancel (suc a) b c = cancel a b c

distrib-lemma : (a b c : ℕ) → (b * a) ∸ (c * a) ≡ (b ∸ c) * a
distrib-lemma a 0      0      = refl
distrib-lemma a 0      (suc c) = 0∸n≡0 (a + c * a)
distrib-lemma a (suc b) 0      = refl
distrib-lemma a (suc b) (suc c) = trans (cancel a (b * a) (c * a)) (distrib-lemma a b c)
