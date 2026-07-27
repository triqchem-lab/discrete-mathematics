{-# OPTIONS --rewriting --guardedness #-}
-- MSC 90 · GF(3)有限全搜索
module Sovereign.Applied.OptimizationDiscrete where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

gradient-zero : T₀ ≡ T₀
gradient-zero = refl
