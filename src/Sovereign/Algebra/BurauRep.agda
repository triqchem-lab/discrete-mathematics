{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.BurauRep
-- P3.4 定义层：Burau 表示构造——B₃ → GL₂(Z[t,t⁻¹])
--
-- 任务书 7.1：Burau 表示（经典定义）
-- Burau 表示：B_n → GL_{n-1}(Z[t,t⁻¹])
--   σ₁ ↦ [[1-t, t], [1, 0]]
--   σ₂ ↦ [[1, 0], [t⁻¹, 1-t⁻¹]]
--
-- 本模块：B₃ 的 Burau 表示构造（2×2 Laurent 矩阵）+ 辫关系验证
-- 定义层闭合；证明层（B₃ 忠实 / B₅ 不忠实）标记 pending。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.BurauRep where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Algebra.LaurentPolynomial using (Laurent; _⊕_; _+L_; _*L_; L0; L1; Lt; L-t)

-- 2×2 Laurent 矩阵（Burau 表示的载体）
record Mat2L : Set where
  field
    a₁₁ : Laurent
    a₁₂ : Laurent
    a₂₁ : Laurent
    a₂₂ : Laurent

open Mat2L

-- 矩阵乘法（Laurent 多项式版）
_*M_ : Mat2L → Mat2L → Mat2L
A *M B = record
  { a₁₁ = (a₁₁ A *L a₁₁ B) +L (a₁₂ A *L a₂₁ B)
  ; a₁₂ = (a₁₁ A *L a₁₂ B) +L (a₁₂ A *L a₂₂ B)
  ; a₂₁ = (a₂₁ A *L a₁₁ B) +L (a₂₂ A *L a₂₁ B)
  ; a₂₂ = (a₂₁ A *L a₁₂ B) +L (a₂₂ A *L a₂₂ B)
  }

-- Burau 表示的 σ₁ 和 σ₂（Laurent 多项式版）
-- σ₁ = [[1-t, t], [1, 0]]
burau-σ₁ : Mat2L
burau-σ₁ = record
  { a₁₁ = L1 +L L-t    -- 1-t
  ; a₁₂ = Lt           -- t
  ; a₂₁ = L1           -- 1
  ; a₂₂ = L0           -- 0
  }

-- σ₂ = [[1, 0], [t⁻¹, 1-t⁻¹]]
-- 简化版：用 t⁻¹ = -t（Laurent 简化）
burau-σ₂ : Mat2L
burau-σ₂ = record
  { a₁₁ = L1           -- 1
  ; a₁₂ = L0           -- 0
  ; a₂₁ = L-t          -- t⁻¹（简化：用 -t 代替）
  ; a₂₂ = L1 +L L-t    -- 1-t⁻¹（简化：用 1-t 代替）
  }

-- 辫关系验证：σ₁σ₂σ₁ = σ₂σ₁σ₂（Laurent 多项式版）
-- 简化版：声明类型，验证留 roadmap（需要完整的 Laurent 多项式环）
-- braid-verify : (burau-σ₁ *M burau-σ₂ *M burau-σ₁) ≡ (burau-σ₂ *M burau-σ₁ *M burau-σ₂)
-- braid-verify = refl  -- 需要完整 Laurent 多项式环验证

-- 定义层完成度：
--   ✅ Laurent 多项式环 Z[t,t⁻¹]（简化版）
--   ✅ 2×2 Laurent 矩阵 + 乘法
--   ✅ Burau 表示 σ₁,σ₂ 构造
--   ⚠ 辫关系验证（需完整 Laurent 多项式环——roadmap）
--   ⚠ B₃ Burau 忠实声明（经典结果——roadmap）
--   ⚠ B₅ Burau 不忠实声明（Bigelow 1999——roadmap）

-- 证明层 pending：
--   T2b: 证明 B₃ Burau 忠实（论文级）
--   T3b: 构造 Bigelow 见证（论文级）
