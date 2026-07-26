{-# OPTIONS --rewriting --guardedness #-}

-- | DiscretePotential — 离散位势论 (MSC 31)
-- GF(3) 格点上的 Laplace 方程 Δu = f.
-- 0 postulate.

module Sovereign.Analysis.DiscretePotential where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)

-- §1. 三点离散 Laplacian ------------------------------------------
-- Δu(i) = u(i-1) + u(i+1) - 2u(i) → 在 GF(3): -2u = T₁·u.
laplace3 : Trit → Trit → Trit → Trit
laplace3 u0 u1 u2 = (u0 ⊕ u2) ⊕ u1  -- u₀+u₂+u₁

-- 常函数在 GF(3) 的 Laplacian = 0
laplace-const : laplace3 T₁ T₁ T₁ ≡ T₀
laplace-const = refl  -- 1+1+1=3≡0 ✓

-- 线性函数 u = [T₀, T₁, T₂] 的 Laplacian
laplace-linear : laplace3 T₀ T₁ T₂ ≡ T₀
laplace-linear = refl  -- 0+2+1=3≡0 ✓

-- 经典位势依赖 ℂ 的 Poisson 核和 Green 函数.
-- 离散替代: GF(3) 上有限差分算子穷举求解.
-- 0 postulate.
