{-# OPTIONS --rewriting --guardedness #-}

-- | S4Burnside —（勘误：旧头注 jac_S4Burnside，名≠模块名，已正名）— S₄ Burnside 验证 · Langlands 第二实例
-- 0 postulate

-- 核心原则：
--   1. S₄ Burnside 计数验证（Langlands 第七例对照面）；
--   2. 实例核对（非一般定理）。
-- 包含：s4-order、s4-burnside
module Sovereign.Problem.Langlands.S4Burnside where

open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ═══════════════════════════════════════════════════════════
-- S₄ 不可约表示: dim ∈ {1,1,2,3,3}, |S₄| = 24
-- Σdim² = 1²+1²+2²+3²+3² = 1+1+4+9+9 = 24 ✓
-- ═══════════════════════════════════════════════════════════

s4-order : ℕ; s4-order = 24
s4-burnside : 1 * 1 + 1 * 1 + 2 * 2 + 3 * 3 + 3 * 3 ≡ 24
s4-burnside = refl

-- Langlands: A₄ (12) + S₄ (24), 两个独立 GL₂(GF(9)) 子群 Burnside 验证
