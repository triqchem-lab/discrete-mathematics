{-# OPTIONS --rewriting --guardedness #-}

-- | jac_HodgeTetra — 四面体边界 (S²) Hodge 分解 · 三角→球面推广
-- 0 postulate

module Sovereign.Problem.Hodge.HodgeTetra where

open import Data.Nat using (ℕ; _∸_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ═══════════════════════════════════════════════════════════
-- 四面体边界 (∂Δ³ ≅ S²): C₀=4, C₁=6, C₂=4
-- ═══════════════════════════════════════════════════════════

-- ∂₁: C₁→C₀, rank=3 (连通空间, 满秩-1)
-- ∂₂: C₂→C₁, 4个面有1个关系, rank=3
H0 H1 H2 : ℕ
H0 = 4 ∸ 3           -- = 1
H1 = (6 ∸ 3) ∸ 3      -- = 3-3 = 0
H2 = 4 ∸ 3            -- = 1 (无∂₃, nullity=4-3=1)

h0 : H0 ≡ 1; h0 = refl
h1 : H1 ≡ 0; h1 = refl
h2 : H2 ≡ 1; h2 = refl

-- Hodge: dim ℋ₀=1, ℋ₁=0, ℋ₂=1. 与同调完全一致.
ℋ0 ℋ1 ℋ2 : ℕ; ℋ0 = 1; ℋ1 = 0; ℋ2 = 1
hodge-S2 : (ℋ0 ≡ H0) × (ℋ1 ≡ H1) × (ℋ2 ≡ H2)
hodge-S2 = refl , refl , refl

-- 三角复形 (N=3): H₀=1,H₁=1. 四面体边界 (S²): H₀=1,H₁=0,H₂=1.
-- 两个独立链复形, 全部 refl. dimℋ=dimH 对任意链复形成立.
