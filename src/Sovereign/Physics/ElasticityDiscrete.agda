{-# OPTIONS --rewriting --guardedness #-}
-- MSC 73 · GF(3)格点弹性
module Sovereign.Physics.ElasticityDiscrete where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

zero-displacement : T₀ ≡ T₀
zero-displacement = refl
