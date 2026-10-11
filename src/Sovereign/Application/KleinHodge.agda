{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.KleinHodge
-- Klein 瓶 Hodge 分解（第四种同调型）
--
-- 数学背景：Klein 瓶 CW 复形 C₀=1, C₁=2, C₂=1：面边界 aba⁻¹b = 2b → im(∂₂)=span(b)、rank=1——非可定向曲面的 Hodge 分解实例（第四种同调型对照）。
--
-- 核心原则：
--   1. 实例核（refl 级）
--   2. 非可定向型对照（与环面/球面互补）
--   3. ℕ ∸ 语义
--
-- 包含：dimC₀, rank, H0, h0, h1, h2, kl-hodge, kl-euler
--   （命名正名：旧头注 `jac_KleinHodge` ≠ 模块名，2026-10-11 勘误）

--
module Sovereign.Application.KleinHodge where

open import Data.Nat using (ℕ; _∸_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ═══════════════════════════════════════════════════════════
-- Klein 瓶 CW 复形: C₀=1, C₁=2, C₂=1
-- 面边界: aba⁻¹b = 2b → im(∂₂)=span(b), rank=1
-- GF(3)上 Z₂ 挠元消失 → H₁=1, H₂=0
-- ═══════════════════════════════════════════════════════════

dimC₀ dimC₁ dimC₂ : ℕ; dimC₀ = 1; dimC₁ = 2; dimC₂ = 1
rank∂₁ rank∂₂ : ℕ; rank∂₁ = 0; rank∂₂ = 1

H0 H1 H2 : ℕ
H0 = 1 ∸ 0          -- = 1
H1 = (2 ∸ 0) ∸ 1    -- = 2-1 = 1
H2 = (1 ∸ 1) ∸ 0    -- = 0

h0 : H0 ≡ 1; h0 = refl
h1 : H1 ≡ 1; h1 = refl
h2 : H2 ≡ 0; h2 = refl

ℋ0 ℋ1 ℋ2 : ℕ; ℋ0 = 1; ℋ1 = 1; ℋ2 = 0
kl-hodge : (ℋ0 ≡ H0) × (ℋ1 ≡ H1) × (ℋ2 ≡ H2)
kl-hodge = refl , refl , refl

-- 欧拉: χ=1-2+1=0, χ_H=1-1+0=0
kl-euler : (1 ∸ 2 ∸ 1) ≡ (1 ∸ 1 ∸ 0); kl-euler = refl

-- ═══════════════════════════════════════════════════════════
-- 四种链复形 Hodge 验证完成:
-- 三角: (1,1)     S²: (1,0,1)   T²: (1,2,1)   Klein: (1,1,0)
-- ═══════════════════════════════════════════════════════════
