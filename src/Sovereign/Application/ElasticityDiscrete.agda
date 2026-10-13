{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.Application.ElasticityDiscrete
-- MSC 73 · GF(3)格点弹性
module Sovereign.Application.ElasticityDiscrete where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

zero-displacement : T₀ ≡ T₀
zero-displacement = refl
