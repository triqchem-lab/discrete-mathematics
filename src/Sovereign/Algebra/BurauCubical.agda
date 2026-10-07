{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Algebra.BurauCubical where

-- | Sovereign.Algebra.BurauCubical
--
-- Burau 表示 B₃ → Mat3(ℤ[t,t⁻¹]) 的函数表示。
--
-- 数学背景：
--   Burau 表示 σᵢ ↦ I_{i-1} ⊕ [[1-t, t],[1, 0]] ⊕ I_{n-i-1}
--   B₃ 生成元（3×3 块嵌入）：
--     σ₁ = [[1,0,0],[0,1-t,t],[0,1,0]]
--     σ₂ = [[1-t,t,0],[1,0,0],[0,0,1]]
--   braid 关系 σ₁σ₂σ₁ = σ₂σ₁σ₂（oracle 已核 t∈[-6,6]，engineering/burau_oracle.py）
--
-- 核心设计：
--   矩阵系数 = Laurent 多项式（LaurentCubical 的函数表示，有限支撑）
--   2×2 变体经 oracle 裁定不满足 braid，弃用（形式化修正记录见台账 Burau.B3GL2.Mat2）

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Int using (ℤ; _+_; _-_; pos; negsuc; sucℤ; predℤ; _+pos_; _+negsuc_; _·_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_; funExt; Σ; _,_)

open import Cubical.Data.Int.Properties using (pos+; injPos)
open import Cubical.Data.Int.Order using (_<_; isIrrefl<; isAsym<)
open import Cubical.Data.Empty using (rec)
open import Sovereign.Algebra.LaurentCubical using (Laurent; IsFinSupp; _+L_; _*L_)

-- ────────────────────────────────────────────────────────────────────
-- Laurent 常量：0、1、t、1-t（系数函数按构造子分派，界证明全 refl）
-- ────────────────────────────────────────────────────────────────────

private
  cf0 : ℤ → ℤ
  cf0 _ = pos zero

  cf0-bnd : IsFinSupp cf0
  cf0-bnd = (pos zero) , (pos zero) , λ _ _ → refl

0L : Laurent
0L = (cf0 , cf0-bnd)

private
  cf1 : ℤ → ℤ
  cf1 (pos zero) = pos (suc zero)
  cf1 (pos (suc n)) = pos zero
  cf1 (negsuc n) = pos zero

  cf1-bnd : IsFinSupp cf1
  cf1-bnd = (pos zero) , (pos zero) , λ { (pos zero) (inl h) → rec {A = cf1 (pos zero) ≡ pos 0} (isIrrefl< {m = pos zero} h) ; (pos zero) (inr h) → rec {A = cf1 (pos zero) ≡ pos 0} (isIrrefl< {m = pos zero} h) ; (pos (suc n)) _ → refl ; (negsuc n) _ → refl }

1L : Laurent
1L = (cf1 , cf1-bnd)

private
  cft : ℤ → ℤ
  cft (pos (suc zero)) = pos (suc zero)
  cft (pos zero) = pos zero
  cft (pos (suc (suc n))) = pos zero
  cft (negsuc n) = pos zero

  cft-bnd : IsFinSupp cft
  cft-bnd = (pos (suc zero)) , (pos (suc zero)) ,
    λ { (pos zero) _ → refl ; (pos (suc zero)) (inl h) → rec {A = cft (pos (suc zero)) ≡ pos 0} (isIrrefl< {m = pos (suc zero)} h) ; (pos (suc zero)) (inr h) → rec {A = cft (pos (suc zero)) ≡ pos 0} (isIrrefl< {m = pos (suc zero)} h) ; (pos (suc (suc n))) _ → refl ; (negsuc n) _ → refl }

tL : Laurent
tL = (cft , cft-bnd)

private
  cfo : ℤ → ℤ
  cfo (pos zero) = pos (suc zero)
  cfo (pos (suc zero)) = negsuc zero
  cfo (pos (suc (suc n))) = pos zero
  cfo (negsuc n) = pos zero

  cfo-bnd : IsFinSupp cfo
  cfo-bnd = (pos zero) , (pos (suc zero)) , cfo-bnd-f
    where
    cfo-bnd-f : ∀ n → (n < pos zero) ⊎ (pos (suc zero) < n) → cfo n ≡ pos 0
    cfo-bnd-f (pos zero) (inl h) = rec {A = cfo (pos zero) ≡ pos zero} (isIrrefl< {m = pos zero} h)
    cfo-bnd-f (pos zero) (inr (i , p)) = rec {A = cfo (pos zero) ≡ pos zero} (isAsym< {m = pos (suc zero)} {n = pos zero} (i , p) (suc zero , refl))
    cfo-bnd-f (pos (suc zero)) (inl (i , p)) = rec {A = cfo (pos (suc zero)) ≡ pos zero} (isAsym< {m = pos (suc zero)} {n = pos zero} (i , p) (suc zero , refl))
    cfo-bnd-f (pos (suc zero)) (inr h) = rec {A = cfo (pos (suc zero)) ≡ pos zero} (isIrrefl< {m = pos (suc zero)} h)
    cfo-bnd-f (pos (suc (suc n))) _ = refl
    cfo-bnd-f (negsuc n) _ = refl
oneMinusT : Laurent
oneMinusT = (cfo , cfo-bnd)

-- ────────────────────────────────────────────────────────────────────
-- 3×3 Laurent 矩阵：9 元组（行主序 a11 a12 a13 a21 a22 a23 a31 a32 a33）
-- ────────────────────────────────────────────────────────────────────

record Mat3 : Set where
  constructor mat3
  field
    a11 a12 a13 a21 a22 a23 a31 a32 a33 : Laurent

id3 : Mat3
id3 = mat3 1L 0L 0L
           0L 1L 0L
           0L 0L 1L

-- 矩阵乘法：c_ij = Σ_k a_ik *L b_kj（Laurent 加法结合序 (x+y)+z）
_*3_ : Mat3 → Mat3 → Mat3
(mat3 a11 a12 a13 a21 a22 a23 a31 a32 a33) *3 (mat3 b11 b12 b13 b21 b22 b23 b31 b32 b33) =
  mat3
    (((a11 *L b11) +L (a12 *L b21)) +L (a13 *L b31))
    (((a11 *L b12) +L (a12 *L b22)) +L (a13 *L b32))
    (((a11 *L b13) +L (a12 *L b23)) +L (a13 *L b33))
    (((a21 *L b11) +L (a22 *L b21)) +L (a23 *L b31))
    (((a21 *L b12) +L (a22 *L b22)) +L (a23 *L b32))
    (((a21 *L b13) +L (a22 *L b23)) +L (a23 *L b33))
    (((a31 *L b11) +L (a32 *L b21)) +L (a33 *L b31))
    (((a31 *L b12) +L (a32 *L b22)) +L (a33 *L b32))
    (((a31 *L b13) +L (a32 *L b23)) +L (a33 *L b33))

-- ────────────────────────────────────────────────────────────────────
-- Burau 生成元（标准 B₃ 块嵌入）
-- ────────────────────────────────────────────────────────────────────

burau-s1 : Mat3
burau-s1 = mat3 1L 0L 0L
                0L oneMinusT tL
                0L 1L 0L

burau-s2 : Mat3
burau-s2 = mat3 oneMinusT tL 0L
                1L 0L 0L
                0L 0L 1L
