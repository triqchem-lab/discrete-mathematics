{-# OPTIONS --guardedness #-}
module test_chiral where
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)

data ChiralSymmetry : Set where
  SingleChiral : ChiralSymmetry

data WuXingAmplitude : Set where
  AmpGenerate : WuXingAmplitude

-- Test 1: pair with explicit _,_
test1 : ChiralSymmetry × WuXingAmplitude
test1 = _,_ SingleChiral AmpGenerate

-- Test 2: let binding
test2 : ChiralSymmetry × WuXingAmplitude
test2 = let s = SingleChiral in (s , AmpGenerate)
