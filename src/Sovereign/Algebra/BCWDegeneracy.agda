{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.BCWDegeneracy
-- 定理二: BCW 矩阵代数的离散离心定理

module Sovereign.Algebra.BCWDegeneracy where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊗_)
open import Sovereign.Algebra.Jacobian.jac_GF3
  using (GF3²; F-gf3; gf3-collision; det-J-formal; J-formal; det2)

-- Fermat 坍缩: y³=y 在 GF(3) 函数空间上
fermat-cubic : ∀ (y : Trit) → ((y ⊗ y) ⊗ y) ≡ y
fermat-cubic T₀ = refl
fermat-cubic T₁ = refl
fermat-cubic T₂ = refl

-- BCW 离心定理: det J = 1 处处成立, 但 F 非单射
BCW-Decoupling : Set
BCW-Decoupling = (∀ (p : GF3²) → det2 (J-formal p) ≡ T₁) × (F-gf3 (T₀ , T₀) ≡ F-gf3 (T₀ , T₁))

proof : BCW-Decoupling
proof = det-J-formal , gf3-collision
