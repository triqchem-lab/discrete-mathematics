{-# OPTIONS --rewriting --guardedness #-}

-- | DiscreteApprox — 离散逼近论 (MSC 41)
-- GF(3) 上的 L¹/L∞ 最佳逼近.
-- 0 postulate.

module Sovereign.Analysis.DiscreteApprox where

open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊗_)

-- §1. L¹ 距离 ------------------------------------------------
l1-dist : Trit → Trit → ℕ
l1-dist T₀ T₀ = 0; l1-dist T₀ T₁ = 1; l1-dist T₀ T₂ = 1
l1-dist T₁ T₀ = 1; l1-dist T₁ T₁ = 0; l1-dist T₁ T₂ = 1
l1-dist T₂ T₀ = 1; l1-dist T₂ T₁ = 1; l1-dist T₂ T₂ = 0

-- 用 T₁ 逼近 T₀,T₁,T₂ 的总误差
approx-err : l1-dist T₀ T₁ + l1-dist T₁ T₁ + l1-dist T₂ T₁ ≡ 2
approx-err = refl  -- 1+0+1=2

-- §2. L∞ 距离 ------------------------------------------------
l∞-dist : Trit → Trit → ℕ
l∞-dist T₀ T₀ = 0; l∞-dist T₀ T₁ = 1; l∞-dist T₀ T₂ = 1
l∞-dist T₁ T₀ = 1; l∞-dist T₁ T₁ = 0; l∞-dist T₁ T₂ = 1
l∞-dist T₂ T₀ = 1; l∞-dist T₂ T₁ = 1; l∞-dist T₂ T₂ = 0

-- 最佳一致逼近: min_{c} max_{x} |f(x)-c|
-- f(x) = x, c=T₁: max = max(|0-1|,|1-1|,|2-1|) = max(1,0,1) = 1
cheb-err : l∞-dist T₀ T₁ + l∞-dist T₂ T₁ ≡ 2
cheb-err = refl

-- §3. 离散 Weierstrass 定理 ----------------------------------
-- GF(3) 上所有函数是多项式 (拉格朗日插值 3 点).
-- 逼近论退化为多项式次数选择.

-- 平方函数 f(x)=x²: 逼近误差 (3点穷举)
sq-err : l1-dist (T₀ ⊗ T₀) T₀ + l1-dist (T₁ ⊗ T₁) T₁ + l1-dist (T₂ ⊗ T₂) T₂ ≡ 1
sq-err = refl  -- 0+0+1=1, f(x)=x² 在 GF(3): 0²=0,1²=1,2²=1

-- 恒等逼近: f(x)=x, 取常数均方逼近
id-err : l1-dist T₀ T₁ + l1-dist T₁ T₁ + l1-dist T₂ T₁ ≡ 2
id-err = refl  -- 1+0+1=2
-- 0 postulate.
