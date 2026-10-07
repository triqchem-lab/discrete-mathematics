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


-- ────────────────────────────────────────────────────────────────────
-- braid 关系：σ₁σ₂σ₁ = σ₂σ₁σ₂（逐 entry funExt，4-case refl）
-- oracle 预核：engineering/burau_oracle.py（t∈[-6,6]）
-- ────────────────────────────────────────────────────────────────────

private
  e11 : Mat3.a11 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a11 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e11 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e12 : Mat3.a12 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a12 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e12 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e13 : Mat3.a13 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a13 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e13 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e21 : Mat3.a21 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a21 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e21 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e22 : Mat3.a22 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a22 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e22 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e23 : Mat3.a23 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a23 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e23 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e31 : Mat3.a31 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a31 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e31 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e32 : Mat3.a32 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a32 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e32 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e33 : Mat3.a33 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a33 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e33 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

-- record 构造子级 9 field 相等组合（9 段单参 cong 链）
mat3-cong : ∀ {a11 a12 a13 a21 a22 a23 a31 a32 a33 b11 b12 b13 b21 b22 b23 b31 b32 b33}
  → a11 ≡ b11 → a12 ≡ b12 → a13 ≡ b13
  → a21 ≡ b21 → a22 ≡ b22 → a23 ≡ b23
  → a31 ≡ b31 → a32 ≡ b32 → a33 ≡ b33
  → mat3 a11 a12 a13 a21 a22 a23 a31 a32 a33 ≡ mat3 b11 b12 b13 b21 b22 b23 b31 b32 b33
mat3-cong {a11} {a12} {a13} {a21} {a22} {a23} {a31} {a32} {a33} {b11} {b12} {b13} {b21} {b22} {b23} {b31} {b32} {b33} p1 p2 p3 p4 p5 p6 p7 p8 p9 =
      cong (λ z → mat3 z a12 a13 a21 a22 a23 a31 a32 a33) p1
  ∙ cong (λ z → mat3 b11 z a13 a21 a22 a23 a31 a32 a33) p2
  ∙ cong (λ z → mat3 b11 b12 z a21 a22 a23 a31 a32 a33) p3
  ∙ cong (λ z → mat3 b11 b12 b13 z a22 a23 a31 a32 a33) p4
  ∙ cong (λ z → mat3 b11 b12 b13 b21 z a23 a31 a32 a33) p5
  ∙ cong (λ z → mat3 b11 b12 b13 b21 b22 z a31 a32 a33) p6
  ∙ cong (λ z → mat3 b11 b12 b13 b21 b22 b23 z a32 a33) p7
  ∙ cong (λ z → mat3 b11 b12 b13 b21 b22 b23 b31 z a33) p8
  ∙ cong (λ z → mat3 b11 b12 b13 b21 b22 b23 b31 b32 z) p9

braid-rel : (burau-s1 *3 burau-s2) *3 burau-s1 ≡ (burau-s2 *3 burau-s1) *3 burau-s2
braid-rel = mat3-cong e11 e12 e13 e21 e22 e23 e31 e32 e33
