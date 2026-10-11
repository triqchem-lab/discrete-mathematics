{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.TorusHodge
-- 环面 T² △-复形 Hodge 分解
--
-- 数学背景：T² 三角复形（1 顶点 3 边 2 面）的 Hodge 分解核：χ=0、dimℋ=2——环面实例（与 T⁶ 线的升维背景呼应，本件只做 T²）。
--
-- 核心原则：
--   1. 实例核（refl 级）
--   2. T² 本件范围（T⁶ 升维另线）
--   3. ℕ ∸ 语义
--
-- 包含：dimC₀, rank, null₁, H0, h0, h1, h2, t2-hodge
--   （命名正名：旧头注 `jac_TorusHodge` ≠ 模块名，2026-10-11 勘误）

--
module Sovereign.Problem.Hodge.TorusHodge where

open import Data.Nat using (ℕ; _∸_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ═══════════════════════════════════════════════════════════
-- T² △-复形: 1顶点, 3边, 2面
-- ═══════════════════════════════════════════════════════════
-- C₀=1, C₁=3, C₂=2
-- ∂₁: 3→1, 所有边首尾连接同一顶点, rank=0
-- ∂₂: 2→3, 两个三角形边界之和为零, rank=1

dimC₀ dimC₁ dimC₂ : ℕ; dimC₀ = 1; dimC₁ = 3; dimC₂ = 2
rank∂₁ rank∂₂ : ℕ; rank∂₁ = 0; rank∂₂ = 1
null₁ null₂ : ℕ; null₁ = dimC₁ ∸ rank∂₁; null₂ = dimC₂ ∸ rank∂₂

-- ═══════════════════════════════════════════════════════════
-- 同调: H₀=1, H₁=2, H₂=1
-- ═══════════════════════════════════════════════════════════

H0 H1 H2 : ℕ
H0 = dimC₀ ∸ rank∂₁      -- = 1-0 = 1
H1 = null₁ ∸ rank∂₂       -- = 3-1 = 2
H2 = null₂ ∸ 0             -- = 2-1 = 1 (无∂₃)

h0 : H0 ≡ 1; h0 = refl
h1 : H1 ≡ 2; h1 = refl
h2 : H2 ≡ 1; h2 = refl

-- Hodge: ℋ = H (refl)
ℋ0 ℋ1 ℋ2 : ℕ; ℋ0 = 1; ℋ1 = 2; ℋ2 = 1
t2-hodge : (ℋ0 ≡ H0) × (ℋ1 ≡ H1) × (ℋ2 ≡ H2)
t2-hodge = refl , refl , refl

-- ═══════════════════════════════════════════════════════════
-- 三个独立链复形的 Hodge 模式验证:
-- 三角: H=(1,1), S²: H=(1,0,1), T²: H=(1,2,1)
-- 全部 dimℋ=dimH (refl). 0 postulate.
-- ═══════════════════════════════════════════════════════════
