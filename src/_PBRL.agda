{-# OPTIONS --cubical --guardedness #-}

-- | _PBRL（⑦B′ 后续件：卷积语义 braid-rel 重证）
--   *3 口径裁决定案（2026-10-11）：卷积形为正式表示层——本件在 _*3cv_（BurauInverse 的
--   窗口卷积矩阵乘，convN 窗 k∈{-1,0,1} 三项）下重证辫关系 σ₁σ₂σ₁ = σ₂σ₁σ₂。
--   范式：9 entry × 6-case 具名子句 funExt（braid-rel 逐点形模板）+ mat3-cong 装配。
module _PBRL where

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; funExt)
open import Sovereign.Algebra.BurauCubical using (Mat3; mat3; burau-s1; burau-s2; mat3-cong)
open import Sovereign.Algebra.BurauInverse using (_*3cv_)

braid-rel-cv : (burau-s1 *3cv (burau-s2 *3cv burau-s1)) ≡ (burau-s2 *3cv (burau-s1 *3cv burau-s2))
braid-rel-cv = mat3-cong e11 e12 e13 e21 e22 e23 e31 e32 e33
  where
    e11' : ∀ n → Mat3.a11 (burau-s1 *3cv (burau-s2 *3cv burau-s1)) n ≡ Mat3.a11 (burau-s2 *3cv (burau-s1 *3cv burau-s2)) n
    e11' (pos zero) = refl
    e11' (pos (suc zero)) = refl
    e11' (pos (suc (suc zero))) = refl
    e11' (pos (suc (suc (suc n)))) = refl
    e11' (negsuc zero) = refl
    e11' (negsuc (suc n)) = refl
    e11 = funExt e11'
    e12' : ∀ n → Mat3.a12 (burau-s1 *3cv (burau-s2 *3cv burau-s1)) n ≡ Mat3.a12 (burau-s2 *3cv (burau-s1 *3cv burau-s2)) n
    e12' (pos zero) = refl
    e12' (pos (suc zero)) = refl
    e12' (pos (suc (suc zero))) = refl
    e12' (pos (suc (suc (suc n)))) = refl
    e12' (negsuc zero) = refl
    e12' (negsuc (suc n)) = refl
    e12 = funExt e12'
    e13' : ∀ n → Mat3.a13 (burau-s1 *3cv (burau-s2 *3cv burau-s1)) n ≡ Mat3.a13 (burau-s2 *3cv (burau-s1 *3cv burau-s2)) n
    e13' (pos zero) = refl
    e13' (pos (suc zero)) = refl
    e13' (pos (suc (suc zero))) = refl
    e13' (pos (suc (suc (suc n)))) = refl
    e13' (negsuc zero) = refl
    e13' (negsuc (suc n)) = refl
    e13 = funExt e13'
    e21' : ∀ n → Mat3.a21 (burau-s1 *3cv (burau-s2 *3cv burau-s1)) n ≡ Mat3.a21 (burau-s2 *3cv (burau-s1 *3cv burau-s2)) n
    e21' (pos zero) = refl
    e21' (pos (suc zero)) = refl
    e21' (pos (suc (suc zero))) = refl
    e21' (pos (suc (suc (suc n)))) = refl
    e21' (negsuc zero) = refl
    e21' (negsuc (suc n)) = refl
    e21 = funExt e21'
    e22' : ∀ n → Mat3.a22 (burau-s1 *3cv (burau-s2 *3cv burau-s1)) n ≡ Mat3.a22 (burau-s2 *3cv (burau-s1 *3cv burau-s2)) n
    e22' (pos zero) = refl
    e22' (pos (suc zero)) = refl
    e22' (pos (suc (suc zero))) = refl
    e22' (pos (suc (suc (suc n)))) = refl
    e22' (negsuc zero) = refl
    e22' (negsuc (suc n)) = refl
    e22 = funExt e22'
    e23' : ∀ n → Mat3.a23 (burau-s1 *3cv (burau-s2 *3cv burau-s1)) n ≡ Mat3.a23 (burau-s2 *3cv (burau-s1 *3cv burau-s2)) n
    e23' (pos zero) = refl
    e23' (pos (suc zero)) = refl
    e23' (pos (suc (suc zero))) = refl
    e23' (pos (suc (suc (suc n)))) = refl
    e23' (negsuc zero) = refl
    e23' (negsuc (suc n)) = refl
    e23 = funExt e23'
    e31' : ∀ n → Mat3.a31 (burau-s1 *3cv (burau-s2 *3cv burau-s1)) n ≡ Mat3.a31 (burau-s2 *3cv (burau-s1 *3cv burau-s2)) n
    e31' (pos zero) = refl
    e31' (pos (suc zero)) = refl
    e31' (pos (suc (suc zero))) = refl
    e31' (pos (suc (suc (suc n)))) = refl
    e31' (negsuc zero) = refl
    e31' (negsuc (suc n)) = refl
    e31 = funExt e31'
    e32' : ∀ n → Mat3.a32 (burau-s1 *3cv (burau-s2 *3cv burau-s1)) n ≡ Mat3.a32 (burau-s2 *3cv (burau-s1 *3cv burau-s2)) n
    e32' (pos zero) = refl
    e32' (pos (suc zero)) = refl
    e32' (pos (suc (suc zero))) = refl
    e32' (pos (suc (suc (suc n)))) = refl
    e32' (negsuc zero) = refl
    e32' (negsuc (suc n)) = refl
    e32 = funExt e32'
    e33' : ∀ n → Mat3.a33 (burau-s1 *3cv (burau-s2 *3cv burau-s1)) n ≡ Mat3.a33 (burau-s2 *3cv (burau-s1 *3cv burau-s2)) n
    e33' (pos zero) = refl
    e33' (pos (suc zero)) = refl
    e33' (pos (suc (suc zero))) = refl
    e33' (pos (suc (suc (suc n)))) = refl
    e33' (negsuc zero) = refl
    e33' (negsuc (suc n)) = refl
    e33 = funExt e33'
