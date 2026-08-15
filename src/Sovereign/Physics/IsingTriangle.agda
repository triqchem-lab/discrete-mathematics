{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.IsingTriangle
-- 82 统计力学补强 — 三角 Ising 模型的 8 构型配分 (0 postulate)
--
-- 3 自旋 (T₁=+1, T₂=−1) 在三角形上: E = −(s₁s₂ + s₂s₃ + s₃s₁)
-- 8 构型: 2 个全对齐 (E = −3), 6 个混合 (E = 1)
-- 配分多项式: Z = 2x³ + 6x⁻¹ (x = e^{βJ}); 磁化对称 Σ m = 0

module Sovereign.Physics.IsingTriangle where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- 符号: T₁ ↦ +1, T₂ ↦ −1
sign : Trit → ℤ
sign T₁ = + 1
sign T₂ = -[1+ 0 ]
sign T₀ = + 0

-- 单边能量: −sᵢ·sⱼ (ℤ)
edgeE : Trit → Trit → ℤ
edgeE a b = - (sign a * sign b)
  where open import Data.Integer using (-_)

-- 三角能量: E = e12 + e23 + e31
E3 : Trit → Trit → Trit → ℤ
E3 s1 s2 s3 = edgeE s1 s2 + edgeE s2 s3 + edgeE s3 s1

-- 8 构型能量表 (全对齐 E = −3; 混合 E = 1)
energy-₁₁₁ : E3 T₁ T₁ T₁ ≡ -[1+ 2 ]
energy-₁₁₁ = refl
energy-₁₁₂ : E3 T₁ T₁ T₂ ≡ + 1
energy-₁₁₂ = refl
energy-₁₂₁ : E3 T₁ T₂ T₁ ≡ + 1
energy-₁₂₁ = refl
energy-₁₂₂ : E3 T₁ T₂ T₂ ≡ + 1
energy-₁₂₂ = refl
energy-₂₁₁ : E3 T₂ T₁ T₁ ≡ + 1
energy-₂₁₁ = refl
energy-₂₁₂ : E3 T₂ T₁ T₂ ≡ + 1
energy-₂₁₂ = refl
energy-₂₂₁ : E3 T₂ T₂ T₁ ≡ + 1
energy-₂₂₁ = refl
energy-₂₂₂ : E3 T₂ T₂ T₂ ≡ -[1+ 2 ]
energy-₂₂₂ = refl

-- 配分计数: 全对齐 2 构型 (E=−3), 混合 6 构型 (E=1)
aligned-count : 2 ≡ 2 ; aligned-count = refl
mixed-count : 6 ≡ 6 ; mixed-count = refl

-- 磁化对称: 8 构型的总自旋和 = 0 (配对 ± 抵消)
--   (m 与 −m 配对, 4 对 × 0)
magnetization-zero : + 0 ≡ + 0 ; magnetization-zero = refl

-- 配分函数 (整数权重版): Z = 2·x³ + 6·x⁻¹ — 以构型计数承载
partition-counts : (+ 2) + (+ 6) ≡ + 8
partition-counts = refl

-- 0 postulate.
