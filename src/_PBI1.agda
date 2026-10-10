{-# OPTIONS --cubical --guardedness #-}

-- | _PBI1（⑦B′ B1-B3：σ₁ 逆元与双侧逆律——**卷积形**；附逐点形反证件）
--
-- 数学：σ₁ = [[1,0,0],[0,1-t,t],[0,1,0]]，2×2 块 [[1-t,t],[1,0]]，det = -t，
--   逆块 = [[0,1],[t⁻¹,t⁻¹(t-1)]]（Laurent 环 t⁻¹ 可逆）⇒ σ₁⁻¹ = [[1,0,0],[0,0,1],[0,t⁻¹,t⁻¹(t-1)]]。
-- ⚠ 语义边界：BurauCubical 的 _*3_ 是**逐点乘**（非卷积）——对它逆律为假
--   （见文末 pointwise-no-inv 注记；n=0 时 (2,2)/(3,2) 两 entry 同位矛盾）。
--   故本件建窗口卷积 _*3cv_（δ 支撑 ⊆ [-1,1] 类专用）证正向律。
module _PBI1 where

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Int using (ℤ; _+_; _-_; _·_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_; funExt)
open import Sovereign.Algebra.BurauCubical
  using (Mat3; mat3; id3; _*3_; burau-s1; burau-s2; mat3-cong; cf0; cf1; cfo; cft)
open import Sovereign.Algebra.LaurentCubical using (sum-ℤ)

-- ── B1 系数函数件 ──────────────────────────────────────────────────

-- t⁻¹ = δ_{-1}
tinv : ℤ → ℤ
tinv (negsuc zero) = pos (suc zero)
tinv (negsuc (suc n)) = pos zero
tinv (pos n) = pos zero

-- t⁻¹(t-1) = δ₀ - δ_{-1}
x33 : ℤ → ℤ
x33 (pos zero) = pos (suc zero)
x33 (pos (suc n)) = pos zero
x33 (negsuc zero) = negsuc zero
x33 (negsuc (suc n)) = pos zero

-- 窗口卷积（窗口 k ∈ [-1,1]；适用于 δ 支撑 ⊆ [-1,1] 的系数函数对）
convN : (ℤ → ℤ) → (ℤ → ℤ) → ℤ → ℤ
convN f g n = sum-ℤ (λ k → f k · g (n - k)) (negsuc 0) (suc (suc zero))

-- 卷积矩阵乘（_*3_ 的卷积版；逐 entry 形与 _*3_ 同构，· 换 convN）
_*3cv_ : Mat3 → Mat3 → Mat3
(mat3 a11 a12 a13 a21 a22 a23 a31 a32 a33) *3cv (mat3 b11 b12 b13 b21 b22 b23 b31 b32 b33) =
  mat3
    (λ n → ((convN a11 b11 n) + (convN a12 b21 n)) + (convN a13 b31 n))
    (λ n → ((convN a11 b12 n) + (convN a12 b22 n)) + (convN a13 b32 n))
    (λ n → ((convN a11 b13 n) + (convN a12 b23 n)) + (convN a13 b33 n))
    (λ n → ((convN a21 b11 n) + (convN a22 b21 n)) + (convN a23 b31 n))
    (λ n → ((convN a21 b12 n) + (convN a22 b22 n)) + (convN a23 b32 n))
    (λ n → ((convN a21 b13 n) + (convN a22 b23 n)) + (convN a23 b33 n))
    (λ n → ((convN a31 b11 n) + (convN a32 b21 n)) + (convN a33 b31 n))
    (λ n → ((convN a31 b12 n) + (convN a32 b22 n)) + (convN a33 b32 n))
    (λ n → ((convN a31 b13 n) + (convN a32 b23 n)) + (convN a33 b33 n))

-- σ₁⁻¹ = [[1,0,0],[0,0,1],[0,t⁻¹,t⁻¹(t-1)]]
s1-inv : Mat3
s1-inv = mat3 cf1 cf0 cf0
              cf0 cf0 cf1
              cf0 tinv x33

-- ── B2/B3 双侧逆律（卷积形；9 entry × 6-case refl——braid-rel 风格）──

s1-inv-r : (burau-s1 *3cv s1-inv) ≡ id3
s1-inv-r = mat3-cong e11 e12 e13 e21 e22 e23 e31 e32 e33
  where
    e11' : ∀ n → Mat3.a11 (burau-s1 *3cv s1-inv) n ≡ Mat3.a11 id3 n
    e11' (pos zero) = refl
    e11' (pos (suc zero)) = refl
    e11' (pos (suc (suc zero))) = refl
    e11' (pos (suc (suc (suc n)))) = refl
    e11' (negsuc zero) = refl
    e11' (negsuc (suc n)) = refl
    e11 = funExt e11'
    e12' : ∀ n → Mat3.a12 (burau-s1 *3cv s1-inv) n ≡ Mat3.a12 id3 n
    e12' (pos zero) = refl
    e12' (pos (suc zero)) = refl
    e12' (pos (suc (suc zero))) = refl
    e12' (pos (suc (suc (suc n)))) = refl
    e12' (negsuc zero) = refl
    e12' (negsuc (suc n)) = refl
    e12 = funExt e12'
    e13' : ∀ n → Mat3.a13 (burau-s1 *3cv s1-inv) n ≡ Mat3.a13 id3 n
    e13' (pos zero) = refl
    e13' (pos (suc zero)) = refl
    e13' (pos (suc (suc zero))) = refl
    e13' (pos (suc (suc (suc n)))) = refl
    e13' (negsuc zero) = refl
    e13' (negsuc (suc n)) = refl
    e13 = funExt e13'
    e21' : ∀ n → Mat3.a21 (burau-s1 *3cv s1-inv) n ≡ Mat3.a21 id3 n
    e21' (pos zero) = refl
    e21' (pos (suc zero)) = refl
    e21' (pos (suc (suc zero))) = refl
    e21' (pos (suc (suc (suc n)))) = refl
    e21' (negsuc zero) = refl
    e21' (negsuc (suc n)) = refl
    e21 = funExt e21'
    e22' : ∀ n → Mat3.a22 (burau-s1 *3cv s1-inv) n ≡ Mat3.a22 id3 n
    e22' (pos zero) = refl
    e22' (pos (suc zero)) = refl
    e22' (pos (suc (suc zero))) = refl
    e22' (pos (suc (suc (suc n)))) = refl
    e22' (negsuc zero) = refl
    e22' (negsuc (suc n)) = refl
    e22 = funExt e22'
    e23' : ∀ n → Mat3.a23 (burau-s1 *3cv s1-inv) n ≡ Mat3.a23 id3 n
    e23' (pos zero) = refl
    e23' (pos (suc zero)) = refl
    e23' (pos (suc (suc zero))) = refl
    e23' (pos (suc (suc (suc n)))) = refl
    e23' (negsuc zero) = refl
    e23' (negsuc (suc n)) = refl
    e23 = funExt e23'
    e31' : ∀ n → Mat3.a31 (burau-s1 *3cv s1-inv) n ≡ Mat3.a31 id3 n
    e31' (pos zero) = refl
    e31' (pos (suc zero)) = refl
    e31' (pos (suc (suc zero))) = refl
    e31' (pos (suc (suc (suc n)))) = refl
    e31' (negsuc zero) = refl
    e31' (negsuc (suc n)) = refl
    e31 = funExt e31'
    e32' : ∀ n → Mat3.a32 (burau-s1 *3cv s1-inv) n ≡ Mat3.a32 id3 n
    e32' (pos zero) = refl
    e32' (pos (suc zero)) = refl
    e32' (pos (suc (suc zero))) = refl
    e32' (pos (suc (suc (suc n)))) = refl
    e32' (negsuc zero) = refl
    e32' (negsuc (suc n)) = refl
    e32 = funExt e32'
    e33' : ∀ n → Mat3.a33 (burau-s1 *3cv s1-inv) n ≡ Mat3.a33 id3 n
    e33' (pos zero) = refl
    e33' (pos (suc zero)) = refl
    e33' (pos (suc (suc zero))) = refl
    e33' (pos (suc (suc (suc n)))) = refl
    e33' (negsuc zero) = refl
    e33' (negsuc (suc n)) = refl
    e33 = funExt e33'

s1-inv-l : (s1-inv *3cv burau-s1) ≡ id3
s1-inv-l = mat3-cong f11 f12 f13 f21 f22 f23 f31 f32 f33
  where
    f11' : ∀ n → Mat3.a11 (s1-inv *3cv burau-s1) n ≡ Mat3.a11 id3 n
    f11' (pos zero) = refl
    f11' (pos (suc zero)) = refl
    f11' (pos (suc (suc zero))) = refl
    f11' (pos (suc (suc (suc n)))) = refl
    f11' (negsuc zero) = refl
    f11' (negsuc (suc n)) = refl
    f11 = funExt f11'
    f12' : ∀ n → Mat3.a12 (s1-inv *3cv burau-s1) n ≡ Mat3.a12 id3 n
    f12' (pos zero) = refl
    f12' (pos (suc zero)) = refl
    f12' (pos (suc (suc zero))) = refl
    f12' (pos (suc (suc (suc n)))) = refl
    f12' (negsuc zero) = refl
    f12' (negsuc (suc n)) = refl
    f12 = funExt f12'
    f13' : ∀ n → Mat3.a13 (s1-inv *3cv burau-s1) n ≡ Mat3.a13 id3 n
    f13' (pos zero) = refl
    f13' (pos (suc zero)) = refl
    f13' (pos (suc (suc zero))) = refl
    f13' (pos (suc (suc (suc n)))) = refl
    f13' (negsuc zero) = refl
    f13' (negsuc (suc n)) = refl
    f13 = funExt f13'
    f21' : ∀ n → Mat3.a21 (s1-inv *3cv burau-s1) n ≡ Mat3.a21 id3 n
    f21' (pos zero) = refl
    f21' (pos (suc zero)) = refl
    f21' (pos (suc (suc zero))) = refl
    f21' (pos (suc (suc (suc n)))) = refl
    f21' (negsuc zero) = refl
    f21' (negsuc (suc n)) = refl
    f21 = funExt f21'
    f22' : ∀ n → Mat3.a22 (s1-inv *3cv burau-s1) n ≡ Mat3.a22 id3 n
    f22' (pos zero) = refl
    f22' (pos (suc zero)) = refl
    f22' (pos (suc (suc zero))) = refl
    f22' (pos (suc (suc (suc n)))) = refl
    f22' (negsuc zero) = refl
    f22' (negsuc (suc n)) = refl
    f22 = funExt f22'
    f23' : ∀ n → Mat3.a23 (s1-inv *3cv burau-s1) n ≡ Mat3.a23 id3 n
    f23' (pos zero) = refl
    f23' (pos (suc zero)) = refl
    f23' (pos (suc (suc zero))) = refl
    f23' (pos (suc (suc (suc n)))) = refl
    f23' (negsuc zero) = refl
    f23' (negsuc (suc n)) = refl
    f23 = funExt f23'
    f31' : ∀ n → Mat3.a31 (s1-inv *3cv burau-s1) n ≡ Mat3.a31 id3 n
    f31' (pos zero) = refl
    f31' (pos (suc zero)) = refl
    f31' (pos (suc (suc zero))) = refl
    f31' (pos (suc (suc (suc n)))) = refl
    f31' (negsuc zero) = refl
    f31' (negsuc (suc n)) = refl
    f31 = funExt f31'
    f32' : ∀ n → Mat3.a32 (s1-inv *3cv burau-s1) n ≡ Mat3.a32 id3 n
    f32' (pos zero) = refl
    f32' (pos (suc zero)) = refl
    f32' (pos (suc (suc zero))) = refl
    f32' (pos (suc (suc (suc n)))) = refl
    f32' (negsuc zero) = refl
    f32' (negsuc (suc n)) = refl
    f32 = funExt f32'
    f33' : ∀ n → Mat3.a33 (s1-inv *3cv burau-s1) n ≡ Mat3.a33 id3 n
    f33' (pos zero) = refl
    f33' (pos (suc zero)) = refl
    f33' (pos (suc (suc zero))) = refl
    f33' (pos (suc (suc (suc n)))) = refl
    f33' (negsuc zero) = refl
    f33' (negsuc (suc n)) = refl
    f33 = funExt f33'

-- ── 逐点形反证件注记（B0-注）────────────────────────────────────────
-- 对现有 _*3_（逐点乘）逆律为假：n = pos zero 处
--   (burau-s1 *3 X) 的 (2,2) ≡ x22(0) 须 = cf1(0) = 1；
--   同时 (3,2) ≡ x22(0) 须 = cf0(0) = 0 ⇒ 1 ≡ 0。
-- 构造性形式待 ·-桥（pos 0 · x ≡ x 形）就位后补：
--   pointwise-no-inv : ∀ (X : Mat3) → ¬ ((burau-s1 *3 X) ≡ id3)
-- 数学矛盾已由上两行钉死（数值面见 oracle 交叉）。
