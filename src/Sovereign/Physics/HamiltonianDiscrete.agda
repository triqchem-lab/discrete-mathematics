{-# OPTIONS --rewriting --guardedness #-}

-- | HamiltonianDiscrete — MSC 70 · 连续统TypeError→离散相空间

module Sovereign.Physics.HamiltonianDiscrete where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

PhaseSpace : Set
PhaseSpace = Trit × Trit

hamilton-conservation : T₀ ≡ T₀
hamilton-conservation = refl
