{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.DiscreteCR
-- 30/32 复分析补强 — GF(3) 离散拉普拉斯与调和性 (0 postulate)
--
-- 连续: f 全纯 ⟹ u = Re f, v = Im f 调和 (Δu = Δv = 0)
-- 离散 GF(3): f = z² (GF(9) 乘法) 的分量满足离散拉普拉斯方程
--   Δu(x,y) = u(x⊕1,y) ⊕ u(x⊖1,y) ⊕ u(x,y⊕1) ⊕ u(x,y⊖1) ⊕ u(x,y) = 0
--   (2 阶差分, 系数 1 求和 — GF(3) 中 1+1+1+1+... 精确)
-- 非调和见证: N(z) = z·σ(z) = x²+y² 不调和 (1 项反证)

module Sovereign.Analysis.DiscreteCR where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

-- z² 的分量: u = x² − y², v = −xy (GF(9) 乘法, α² = −1)
u : Trit → Trit → Trit
u x y = (x ⊗ x) ⊕ negate (y ⊗ y)

v : Trit → Trit → Trit
v x y = negate (x ⊗ y)

-- 离散拉普拉斯: Δf = f(x⊕1) ⊕ f(x⊖1) ⊕ f(y⊕1) ⊕ f(y⊖1) ⊕ f
Δ : (Trit → Trit → Trit) → Trit → Trit → Trit
Δ f x y =
  ((((f (x ⊕ T₁) y) ⊕ (f (x ⊕ T₂) y)) ⊕ (f x (y ⊕ T₁))) ⊕ (f x (y ⊕ T₂)))
  ⊕ (T₂ ⊗ f x y)

-- z² 调和: Δu = 0 (9 项)
harmonic-u : ∀ x y → Δ u x y ≡ T₀
harmonic-u T₀ T₀ = refl
harmonic-u T₀ T₁ = refl
harmonic-u T₀ T₂ = refl
harmonic-u T₁ T₀ = refl
harmonic-u T₁ T₁ = refl
harmonic-u T₁ T₂ = refl
harmonic-u T₂ T₀ = refl
harmonic-u T₂ T₁ = refl
harmonic-u T₂ T₂ = refl

harmonic-v : ∀ x y → Δ v x y ≡ T₀
harmonic-v T₀ T₀ = refl
harmonic-v T₀ T₁ = refl
harmonic-v T₀ T₂ = refl
harmonic-v T₁ T₀ = refl
harmonic-v T₁ T₁ = refl
harmonic-v T₁ T₂ = refl
harmonic-v T₂ T₀ = refl
harmonic-v T₂ T₁ = refl
harmonic-v T₂ T₂ = refl

-- 范数 N(z) = x²+y² 不调和: 见证 (1,0) — ΔN(1,0) = 2 ≢ 0
n : Trit → Trit → Trit
n x y = (x ⊗ x) ⊕ (y ⊗ y)

not-harmonic-n : ¬ (Δ n T₁ T₀ ≡ T₀)
not-harmonic-n ()

-- 0 postulate.
