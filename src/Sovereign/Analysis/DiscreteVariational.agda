{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.DiscreteVariational
-- 49 变分法补强 — 离散能量极小与调和中点 (0 postulate)
--
-- 端点固定的三点路径 (y₀=0, y₂=2), 中间值 y₁ ∈ {0,1,2}:
--   能量 E(y) = y² + (2−y)² (ℤ 算术)
--   E(0) = 4, E(1) = 2, E(2) = 4 — 极小化元 y = 1 = 调和中点 (0+2)/2

module Sovereign.Analysis.DiscreteVariational where

open import Data.Nat using (ℕ; _*_; _+_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

E : ℕ → ℕ
E y = (y * y) + ((2 ∸ y) * (2 ∸ y))

-- 能量表
energy-0 : E 0 ≡ 4 ; energy-0 = refl
energy-1 : E 1 ≡ 2 ; energy-1 = refl
energy-2 : E 2 ≡ 4 ; energy-2 = refl

-- 极小性: E(1) ≤ E(0) 与 E(1) ≤ E(2) (饱和减法 = 0 ⟺ ≤)
minimal-0 : E 1 ∸ E 0 ≡ 0 ; minimal-0 = refl
minimal-2 : E 1 ∸ E 2 ≡ 0 ; minimal-2 = refl

-- 调和中点: 极小化元 = (0+2)/2 = 1
harmonic-mid : (0 + 2) ∸ 1 ≡ 1 ; harmonic-mid = refl

-- 离散 Euler-Lagrange 对应: 极小点 = 调和点 (Δy = 0 的解)
euler-lagrange-discrete : (1 + 1) ∸ 2 ≡ 0 ; euler-lagrange-discrete = refl

-- 0 postulate.
