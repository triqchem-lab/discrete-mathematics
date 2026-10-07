{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Algebra.BurauCubical where

-- | Sovereign.Algebra.BurauCubical
--
-- Burau 表示 B₃ → Mat3(ℤ[t,t⁻¹]) 的函数表示（裸系数函数版，沿 LaurentCubical
-- 「逐点相等避 funExt 类型推断问题」先例——Mat3 系数取 ℤ→ℤ，IsFinSupp 不进矩阵层）。
--
-- 数学背景：
--   Burau 表示 σᵢ ↦ I_{i-1} ⊕ [[1-t, t],[1, 0]] ⊕ I_{n-i-1}
--   B₃ 生成元（3×3 块嵌入）：
--     σ₁ = [[1,0,0],[0,1-t,t],[0,1,0]]
--     σ₂ = [[1-t,t,0],[1,0,0],[0,0,1]]
--   braid 关系 σ₁σ₂σ₁ = σ₂σ₁σ₂（oracle 已核 t∈[-6,6]，engineering/burau_oracle.py）
--   2×2 变体经 oracle 裁定不满足 braid，弃用（台账 Burau.B3GL2.Mat2 形式化修正记录）

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Int using (ℤ; _+_; _-_; _·_; pos; negsuc; sucℤ; predℤ; _+pos_; _+negsuc_)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_; funExt)

-- ────────────────────────────────────────────────────────────────────
-- 系数函数常量：0、1、t、1-t（按 ℤ 构造子分派）
-- ────────────────────────────────────────────────────────────────────

cf0 : ℤ → ℤ
cf0 _ = pos zero

cf1 : ℤ → ℤ
cf1 (pos zero) = pos (suc zero)
cf1 (pos (suc n)) = pos zero
cf1 (negsuc n) = pos zero

cft : ℤ → ℤ
cft (pos (suc zero)) = pos (suc zero)
cft (pos zero) = pos zero
cft (pos (suc (suc n))) = pos zero
cft (negsuc n) = pos zero

cfo : ℤ → ℤ
cfo (pos zero) = pos (suc zero)
cfo (pos (suc zero)) = negsuc zero
cfo (pos (suc (suc n))) = pos zero
cfo (negsuc n) = pos zero

-- ────────────────────────────────────────────────────────────────────
-- 3×3 矩阵：record 9 系数函数（行主序）
-- ────────────────────────────────────────────────────────────────────

record Mat3 : Set where
  constructor mat3
  field
    a11 a12 a13 a21 a22 a23 a31 a32 a33 : ℤ → ℤ

id3 : Mat3
id3 = mat3 cf1 cf0 cf0
           cf0 cf1 cf0
           cf0 cf0 cf1

-- 矩阵乘法：c_ij = Σ_k a_ik * b_kj（Int 算术，加法结合序 (x+y)+z）
_*3_ : Mat3 → Mat3 → Mat3
(mat3 a11 a12 a13 a21 a22 a23 a31 a32 a33) *3 (mat3 b11 b12 b13 b21 b22 b23 b31 b32 b33) =
  mat3
    (λ n → ((a11 n · b11 n) + (a12 n · b21 n)) + (a13 n · b31 n))
    (λ n → ((a11 n · b12 n) + (a12 n · b22 n)) + (a13 n · b32 n))
    (λ n → ((a11 n · b13 n) + (a12 n · b23 n)) + (a13 n · b33 n))
    (λ n → ((a21 n · b11 n) + (a22 n · b21 n)) + (a23 n · b31 n))
    (λ n → ((a21 n · b12 n) + (a22 n · b22 n)) + (a23 n · b32 n))
    (λ n → ((a21 n · b13 n) + (a22 n · b23 n)) + (a23 n · b33 n))
    (λ n → ((a31 n · b11 n) + (a32 n · b21 n)) + (a33 n · b31 n))
    (λ n → ((a31 n · b12 n) + (a32 n · b22 n)) + (a33 n · b32 n))
    (λ n → ((a31 n · b13 n) + (a32 n · b23 n)) + (a33 n · b33 n))

-- ────────────────────────────────────────────────────────────────────
-- Burau 生成元（标准 B₃ 块嵌入）
-- ────────────────────────────────────────────────────────────────────

burau-s1 : Mat3
burau-s1 = mat3 cf1 cf0 cf0
                cf0 cfo cft
                cf0 cf1 cf0

burau-s2 : Mat3
burau-s2 = mat3 cfo cft cf0
                cf1 cf0 cf0
                cf0 cf0 cf1
