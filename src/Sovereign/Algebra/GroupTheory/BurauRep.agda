{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BurauRep
-- P3.4 定义层：Burau 表示构造——B₃ → GL₂(Z[t,t⁻¹])
--
-- 任务书 7.1：Burau 表示（经典定义）
-- Burau 表示：B_n → GL_{n-1}(Z[t,t⁻¹])
--   σ₁ ↦ [[-t, 1], [0, 1]]
--   σ₂ ↦ [[1, 0], [t, -t]]
--
-- 本模块：B₃ 的 Burau 表示构造（2×2 Laurent 矩阵）+ 辫关系验证
-- 定义层闭合；证明层（B₃ 忠实 / B₅ 不忠实）标记 pending。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.GroupTheory.BurauRep where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- 【2026-10-10 裁决 ⑤】Laurent 多项式改函数表示（LaurentCubical：ℤ[t,t⁻¹] = {f : ℤ → ℤ | 有限支撑}，本源）
--   原 List 投影（LaurentPolynomial 简化截断环）已归档——见 docs/decisions/数学严谨性路线选择-2026-10-10.md §⑤
open import Sovereign.Algebra.RingTheory.LaurentCubical using (Laurent; _+L_; _*L_; R0; R1; tvar; tneg)

-- 常量别名（保持 Burau 矩阵定义处的书写惯例：L0=0, L1=1, Lt=t, L-t=-t）
L0 L1 Lt L-t : Laurent
L0 = R0
L1 = R1
Lt = tvar
L-t = tneg

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

-- Burau 表示的 σ₁ 和 σ₂（正确的经典形式）
-- σ₁ = [[-t, 1], [0, 1]]
burau-σ₁ : Mat2L
burau-σ₁ = record
  { a₁₁ = L-t          -- -t
  ; a₁₂ = L1           -- 1
  ; a₂₁ = L0           -- 0
  ; a₂₂ = L1           -- 1
  }

-- σ₂ = [[1, 0], [t, -t]]
burau-σ₂ : Mat2L
burau-σ₂ = record
  { a₁₁ = L1           -- 1
  ; a₁₂ = L0           -- 0
  ; a₂₁ = Lt           -- t
  ; a₂₂ = L-t          -- -t
  }

-- 辫关系验证：σ₁σ₂σ₁ = σ₂σ₁σ₂
-- 计算 σ₁σ₂σ₁：
-- σ₁σ₂ = [[-t, 1], [0, 1]] × [[1, 0], [t, -t]]
--       = [[-t*1 + 1*t, -t*0 + 1*(-t)], [0*1 + 1*t, 0*0 + 1*(-t)]]
--       = [[-t+t, -t], [t, -t]]
--       = [[0, -t], [t, -t]]
-- σ₁σ₂σ₁ = [[0, -t], [t, -t]] × [[-t, 1], [0, 1]]
--         = [[0*(-t) + (-t)*0, 0*1 + (-t)*1], [t*(-t) + (-t)*0, t*1 + (-t)*1]]
--         = [[0, -t], [-t², t-t]]
--         = [[0, -t], [-t², 0]]
--
-- 计算 σ₂σ₁σ₂：
-- σ₂σ₁ = [[1, 0], [t, -t]] × [[-t, 1], [0, 1]]
--       = [[1*(-t) + 0*0, 1*1 + 0*1], [t*(-t) + (-t)*0, t*1 + (-t)*1]]
--       = [[-t, 1], [-t², t-t]]
--       = [[-t, 1], [-t², 0]]
-- σ₂σ₁σ₂ = [[-t, 1], [-t², 0]] × [[1, 0], [t, -t]]
--         = [[-t*1 + 1*t, -t*0 + 1*(-t)], [-t²*1 + 0*t, -t²*0 + 0*(-t)]]
--         = [[-t+t, -t], [-t², 0]]
--         = [[0, -t], [-t², 0]]
--
-- 两边相等：[[0, -t], [-t², 0]] = [[0, -t], [-t², 0]] ✓
--
-- 【2026-10-11 状态更新】⑦A 环公理已闭合（A.laurent-ring-laws proven，回执 5fefb4cc）；
--   σ⁻¹ 逆律已证（BurauInverse 卷积语义 *_*3cv_/_*3c_*，回执 28909852）——
--   原「⑦A 完成前不声称 σ⁻¹ 逆性质」边界**解除**。
--   辫关系：逐点形已证（BurauCubical.braid-rel，回执 ae8696b6）；卷积形重证排期中。
-- 当前版本：逆律已证（卷积语义）；braid-rel 卷积形待重证

-- 辫关系声明（类型级——验证依赖 *L 环公理，见 ⑦A 排期节点）
braid-rel-type : Set
braid-rel-type = (burau-σ₁ *M (burau-σ₂ *M burau-σ₁)) ≡ (burau-σ₂ *M (burau-σ₁ *M burau-σ₂))

-- 具体数值验证（取 t=2，用 ℤ 矩阵）
-- σ₁ = [[-2, 1], [0, 1]], σ₂ = [[1, 0], [2, -2]]
-- σ₁σ₂σ₁ = [[0, -2], [-4, 0]] = σ₂σ₁σ₂ ✓

-- Faithful/Unfaithful 谓词定义（roadmap）
-- Faithful ρ = ∀ β → ρ β ≡ 1ₘ → β ≡ 1
-- Unfaithful ρ = ∃ β → β ≢ 1 × ρ β ≡ 1ₘ

-- 【⑦B 数学边界（2026-10-10 人类裁决，显式陈述）】
--   历史事实（已归档的 LaurentPolynomial 简化截断环）：_*L_ 丢 t² 项、t⁻¹ 不存在、det = −t 不可逆
--     → σ₁⁻¹ = [[-t⁻¹, t⁻¹], [0, 1]] 在该环上无法构造——这是真实数学边界，不是「未完成」。
--   现状（⑤ 迁移后，函数表示 ℤ[t,t⁻¹]）：t⁻¹ 可表（mono (pos 1) (negsuc 0)），σ₁⁻¹ 表示层可构造；
--     其**逆律**（σ₁·σ₁⁻¹ = I）依赖的 *L 环公理已闭合（⑦A，回执 5fefb4cc）——
--     逆律已在 BurauInverse 证毕（卷积语义，回执 28909852）；本文件的「不声称」边界解除。
--
-- 定义层完成度：
--   ✅ Laurent 多项式环 Z[t,t⁻¹]（函数表示，LaurentCubical）
--   ✅ 2×2 Laurent 矩阵 + 乘法（真卷积 *L）
--   ✅ Burau 表示 σ₁,σ₂ 构造（正确的经典形式）
--   ✅ 辫关系类型声明 / Faithful 谓词定义
--   ✅ σ⁻¹ 逆律（BurauInverse，卷积语义——回执 28909852）
--   ✅ 辫关系·逐点形（BurauCubical.braid-rel——回执 ae8696b6；⚠ 逐点乘 *_*3_* 非环乘，措辞已限定）
--   ⏳ 辫关系·卷积形（*3 口径裁决定案：双轨并存，卷积形为正式表示层——重证排期中）
--   ⚠ B₃ Burau 忠实声明（经典结果——roadmap）
--   ⚠ B₅ Burau 不忠实声明（Bigelow 1999——roadmap）

-- 证明层 pending：
--   T2b: 证明 B₃ Burau 忠实（论文级）
--   T3b: 构造 Bigelow 见证（论文级）
