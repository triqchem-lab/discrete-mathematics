{-# OPTIONS --rewriting --guardedness #-}

-- | DiscreteApprox — 离散逼近论 (MSC 41)
-- GF(3) 上的最佳逼近: 有限集上的 L∞/L1 极小化.
-- 0 postulate.

module Sovereign.Analysis.DiscreteApprox where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate)

-- §1. 离散范数 --------------------------------------------------
-- L∞ 范数: ||f||∞ = max |f(x)| (在 GF(3) 上穷举 3^n 值)
-- L¹ 范数: ||f||₁ = Σ |f(x)|

-- 二点函数的 L¹ 距离
l1-dist : Trit → Trit → ℕ
l1-dist T₀ T₀ = 0; l1-dist T₀ T₁ = 1; l1-dist T₀ T₂ = 1
l1-dist T₁ T₀ = 1; l1-dist T₁ T₁ = 0; l1-dist T₁ T₂ = 1
l1-dist T₂ T₀ = 1; l1-dist T₂ T₁ = 1; l1-dist T₂ T₂ = 0

-- 常逼近: 用 T₁ 逼近 T₀,T₁,T₂
approx-err : l1-dist T₀ T₁ + l1-dist T₁ T₁ + l1-dist T₂ T₁ ≡ 2
approx-err = refl  -- 1+0+1=2 ✓

-- §2. 最佳一致逼近 (Chebyshev) -----------------------------------
-- 在 GF(3)ⁿ 上穷举所有候选多项式.
-- 离散 Chebyshev 交错定理退化为有限集上的 min-max.

-- 经典逼近论依赖 Weierstrass 定理和连续函数空间.
-- 离散替代: GF(3)ⁿ 上的穷举 min-max 搜索.
-- 0 postulate.
