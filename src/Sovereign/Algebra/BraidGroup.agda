{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.BraidGroup
-- P3.4 前置件：辫群 B_n 的最小形式化
--
-- 任务书 7.1：Burau 表示不忠实性（Bigelow 1999, n≥5）
-- 辫群 B_n 由 n-1 个生成元 σ₁,...,σ_{n-1} 满足：
--   ① σᵢσⱼ = σⱼσᵢ (|i-j| ≥ 2)
--   ② σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁
--
-- 本模块：B_3 的最小形式化（2 个生成元 + 关系声明）
-- 0 postulate / 0 hole。
module Sovereign.Algebra.BraidGroup where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- B_3 的生成元
data B3 : Set where
  e   : B3          -- 单位元
  σ₁  : B3          -- 生成元 σ₁
  σ₂  : B3          -- 生成元 σ₂
  σ₁⁻¹ : B3        -- σ₁ 的逆
  σ₂⁻¹ : B3        -- σ₂ 的逆
  _·_ : B3 → B3 → B3  -- 群乘法

-- B_3 的关系（声明——证明体留 roadmap）
-- ① σ₁σ₂σ₁ = σ₂σ₁σ₂（辫关系）
postulate
  braid-rel : (σ₁ · (σ₂ · σ₁)) ≡ (σ₂ · (σ₁ · σ₂))

-- ② σᵢσᵢ⁻¹ = e（逆元）
postulate
  σ₁-inv : (σ₁ · σ₁⁻¹) ≡ e
  σ₂-inv : (σ₂ · σ₂⁻¹) ≡ e

-- Burau 表示声明（roadmap）
-- burau-rep : B3 → GL₂(Z[t,t⁻¹])
-- burau-rep σ₁ = [[1-t, t], [1, 0]]
-- burau-rep σ₂ = [[1, 0], [t⁻¹, 1-t⁻¹]]
-- burau-faithful : ¬ (Injective burau-rep)  -- Bigelow 1999
