{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Algebra.BurauInverse
-- Burau 生成元逆元（双轨层）：①卷积语义（_*3cv_ / _*3c_）下 σ₁⁻¹/σ₂⁻¹ 双侧逆律全形；
--   ②逐点语义（BurauCubical._*3_）下逆律**不可能**（构造性反证件）。
-- 数学背景：σ₁ 块 [[1-t,t],[1,0]] det=−t 在 ℤ[t,t⁻¹] 可逆，逆块 [[0,1],[t⁻¹,t⁻¹(t-1)]]。
--   真表示语义 = Laurent 环乘法（卷积）；`_*3_` 逐点乘非环乘（口径裁决开立中）。
-- 核心原则：1. 双轨并存，不动 BurauCubical 既有件；2. 反证件与正律同库，禁假证明；
--   3. t·t⁻¹≡1 泛形复用 LaurentRingLaws（t-tinv），此处只做 δ 具体例。
module Sovereign.Algebra.BurauInverse where


-- | _PBI1（⑦B′ B1-B3：σ₁ 逆元与双侧逆律——**卷积形**；附逐点形反证件）
--
-- 数学：σ₁ = [[1,0,0],[0,1-t,t],[0,1,0]]，2×2 块 [[1-t,t],[1,0]]，det = -t，
--   逆块 = [[0,1],[t⁻¹,t⁻¹(t-1)]]（Laurent 环 t⁻¹ 可逆）⇒ σ₁⁻¹ = [[1,0,0],[0,0,1],[0,t⁻¹,t⁻¹(t-1)]]。
-- ⚠ 语义边界：BurauCubical 的 _*3_ 是**逐点乘**（非卷积）——对它逆律为假
--   （见文末 pointwise-no-inv 注记；n=0 时 (2,2)/(3,2) 两 entry 同位矛盾）。
--   故本件建窗口卷积 _*3cv_（δ 支撑 ⊆ [-1,1] 类专用）证正向律。

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Int using (ℤ; _+_; _-_; _·_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_; funExt)
open import Sovereign.Algebra.BurauCubical
  using (Mat3; mat3; id3; _*3_; burau-s1; burau-s2; mat3-cong; cf0; cf1; cfo; cft)
open import Sovereign.Algebra.LaurentCubical using (sum-ℤ)

-- ── B1 系数函数件 ──────────────────────────────────────────────────

-- t⁻¹ = δ_{-1}
tinv-fn : ℤ → ℤ
tinv-fn (negsuc zero) = pos (suc zero)
tinv-fn (negsuc (suc n)) = pos zero
tinv-fn (pos n) = pos zero

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
              cf0 tinv-fn x33

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


-- | _PBI2（⑦B′ 子件 B4：σ₂ 块逆律——陈述体检 + 卷积修正版双交付）
--
-- ⚠ 任务书陈述体检：`(burau-s2 *3 s2-inv) ≡ id3` 按 _*3_（BurauCubical 的逐点系数乘法）为**假**：
--   n=0 处 burau-s2 系数阵 = [[1,0,0],[1,0,0],[0,0,1]]，前两行相同 ⇒ 乘积前两行恒同 ⇒ 永不等于 id3。
--   本件双交付：① 不可能性证书 no-right-inv / no-left-inv（statement_wrong 证据）；
--   ② 卷积语义（Laurent 环）修正版：_*3c_ 矩阵乘 + s2-inv + s2-inv-r / s2-inv-l（真逆律）。
-- 一般层 t·t⁻¹=1 与 mono-conv 在 Sovereign.Algebra.LaurentRingLaws（t-tinv/tinv-t/mono-conv），
-- 本件为其 δ 具体例（refl 级，不重证泛形）。

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; funExt; _∙_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Int using (ℤ; pos; negsuc; _+_; _·_; _-_)
open import Cubical.Data.Int.Properties using (injPos; ·AnnihilR)
open import Cubical.Data.Nat using (ℕ; zero; suc; snotz)
open import Sovereign.Algebra.BurauCubical
  using (Mat3; mat3; _*3_; burau-s2; id3; cf0; cf1; cfo; cft; mat3-cong)
open import Sovereign.Algebra.LaurentCubical using (sums; tvar; R1; _*L_)
open import Sovereign.Algebra.LaurentRingLaws using (tinv; t-tinv)

-- ────────────────────────────────────────────────────────────────────
-- ① 逐点版不可能性证书（任务书原陈述 = 假）
-- ────────────────────────────────────────────────────────────────────

1≢0 : pos (suc zero) ≡ pos zero → ⊥
1≢0 e = snotz (injPos e)

0≢1 : pos zero ≡ pos (suc zero) → ⊥
0≢1 e = 1≢0 (sym e)

-- 右逆不可能：(burau-s2 *3 X) 的 11 与 21 元在 n=0 同值，与 id3 矛盾
no-right-inv : ∀ (X : Mat3) → (burau-s2 *3 X) ≡ id3 → ⊥
no-right-inv (mat3 b11 b12 b13 b21 b22 b23 b31 b32 b33) e = 1≢0 (sym h11 ∙ h21)
  where
  h11 : b11 (pos zero) ≡ pos (suc zero)
  h11 = cong (λ M → Mat3.a11 M (pos zero)) e
  h21 : b11 (pos zero) ≡ pos zero
  h21 = cong (λ M → Mat3.a21 M (pos zero)) e

-- 左逆不可能：(X *3 burau-s2) 的 22 元在 n=0 归零，与 id3 的 1 矛盾
no-left-inv : ∀ (X : Mat3) → (X *3 burau-s2) ≡ id3 → ⊥
no-left-inv (mat3 b11 b12 b13 b21 b22 b23 b31 b32 b33) e = 0≢1 (sym d22 ∙ h22)
  where
  h22 : ((b21 (pos zero) · pos zero) + (b22 (pos zero) · pos zero)) + (b23 (pos zero) · pos zero)
      ≡ pos (suc zero)
  h22 = cong (λ M → Mat3.a22 M (pos zero)) e
  z1 : ∀ x → x · pos zero ≡ pos zero
  z1 = ·AnnihilR
  d22 : ((b21 (pos zero) · pos zero) + (b22 (pos zero) · pos zero)) + (b23 (pos zero) · pos zero)
      ≡ pos zero
  d22 =
      cong (λ w → (w + (b22 (pos zero) · pos zero)) + (b23 (pos zero) · pos zero)) (z1 (b21 (pos zero)))
    ∙ cong (λ w → (pos zero + w) + (b23 (pos zero) · pos zero)) (z1 (b22 (pos zero)))
    ∙ cong (λ w → (pos zero + pos zero) + w) (z1 (b23 (pos zero)))

-- ────────────────────────────────────────────────────────────────────
-- ② 卷积语义修正版（Laurent 环——真逆律）
--    t⁻¹ = δ₋₁，1 − t⁻¹ = δ₀ − δ₋₁；块逆 [[0,1],[t⁻¹, 1−t⁻¹]]（左上 2×2，第三对角 1）
-- ────────────────────────────────────────────────────────────────────

cf-tinv : ℤ → ℤ
cf-tinv (pos zero) = pos zero
cf-tinv (pos (suc n)) = pos zero
cf-tinv (negsuc zero) = pos (suc zero)
cf-tinv (negsuc (suc n)) = pos zero

cf-1tinv : ℤ → ℤ
cf-1tinv (pos zero) = pos (suc zero)
cf-1tinv (pos (suc n)) = pos zero
cf-1tinv (negsuc zero) = negsuc zero
cf-1tinv (negsuc (suc n)) = pos zero

s2-inv : Mat3
s2-inv = mat3 cf0 cf1 cf0
              cf-tinv cf-1tinv cf0
              cf0 cf0 cf1

-- 卷积（三项窗 k ∈ {negsuc zero, pos zero, pos 1} = {−1,0,1}，覆盖全部支撑；注意 negsuc n = −(n+1)）：(f ⋆ g)(n) = Σ_k f k · g (n − k)
convF : (ℤ → ℤ) → (ℤ → ℤ) → ℤ → ℤ
convF f g n =
  ((f (negsuc zero) · g (n - negsuc zero)) + (f (pos zero) · g n)) + (f (pos 1) · g (n - pos 1))

-- 矩阵卷积乘：(A ⋆ B)_ij = Σ_k A_ik ⋆ B_kj（系数函数卷积 + 逐点加）
_*3c_ : Mat3 → Mat3 → Mat3
(mat3 a11 a12 a13 a21 a22 a23 a31 a32 a33) *3c (mat3 b11 b12 b13 b21 b22 b23 b31 b32 b33) =
  mat3
    (λ n → (convF a11 b11 n + convF a12 b21 n) + convF a13 b31 n)
    (λ n → (convF a11 b12 n + convF a12 b22 n) + convF a13 b32 n)
    (λ n → (convF a11 b13 n + convF a12 b23 n) + convF a13 b33 n)
    (λ n → (convF a21 b11 n + convF a22 b21 n) + convF a23 b31 n)
    (λ n → (convF a21 b12 n + convF a22 b22 n) + convF a23 b32 n)
    (λ n → (convF a21 b13 n + convF a22 b23 n) + convF a23 b33 n)
    (λ n → (convF a31 b11 n + convF a32 b21 n) + convF a33 b31 n)
    (λ n → (convF a31 b12 n + convF a32 b22 n) + convF a33 b32 n)
    (λ n → (convF a31 b13 n + convF a32 b23 n) + convF a33 b33 n)

-- 交叉锚（泛形在 LaurentRingLaws，勿重证）：本件 (s2 ⋆ s2-inv)₁₁ = t·t⁻¹ 的 δ 特例
t-tinv-anchor : ∀ n → sums n (tvar *L tinv) ≡ sums n R1
t-tinv-anchor = t-tinv

-- 右逆：burau-s2 ⋆ s2-inv = id3（9 entry × 5-case refl，仿 braid-rel 模板）
private
  r11 : Mat3.a11 (burau-s2 *3c s2-inv) ≡ Mat3.a11 id3
  r11 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  r12 : Mat3.a12 (burau-s2 *3c s2-inv) ≡ Mat3.a12 id3
  r12 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  r13 : Mat3.a13 (burau-s2 *3c s2-inv) ≡ Mat3.a13 id3
  r13 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  r21 : Mat3.a21 (burau-s2 *3c s2-inv) ≡ Mat3.a21 id3
  r21 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  r22 : Mat3.a22 (burau-s2 *3c s2-inv) ≡ Mat3.a22 id3
  r22 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  r23 : Mat3.a23 (burau-s2 *3c s2-inv) ≡ Mat3.a23 id3
  r23 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  r31 : Mat3.a31 (burau-s2 *3c s2-inv) ≡ Mat3.a31 id3
  r31 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  r32 : Mat3.a32 (burau-s2 *3c s2-inv) ≡ Mat3.a32 id3
  r32 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  r33 : Mat3.a33 (burau-s2 *3c s2-inv) ≡ Mat3.a33 id3
  r33 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }

s2-inv-r : (burau-s2 *3c s2-inv) ≡ id3
s2-inv-r = mat3-cong r11 r12 r13 r21 r22 r23 r31 r32 r33

-- 左逆：s2-inv ⋆ burau-s2 = id3
private
  l11 : Mat3.a11 (s2-inv *3c burau-s2) ≡ Mat3.a11 id3
  l11 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  l12 : Mat3.a12 (s2-inv *3c burau-s2) ≡ Mat3.a12 id3
  l12 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  l13 : Mat3.a13 (s2-inv *3c burau-s2) ≡ Mat3.a13 id3
  l13 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  l21 : Mat3.a21 (s2-inv *3c burau-s2) ≡ Mat3.a21 id3
  l21 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  l22 : Mat3.a22 (s2-inv *3c burau-s2) ≡ Mat3.a22 id3
  l22 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  l23 : Mat3.a23 (s2-inv *3c burau-s2) ≡ Mat3.a23 id3
  l23 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  l31 : Mat3.a31 (s2-inv *3c burau-s2) ≡ Mat3.a31 id3
  l31 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  l32 : Mat3.a32 (s2-inv *3c burau-s2) ≡ Mat3.a32 id3
  l32 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }
  l33 : Mat3.a33 (s2-inv *3c burau-s2) ≡ Mat3.a33 id3
  l33 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc zero) → refl ; (negsuc (suc n)) → refl }

s2-inv-l : (s2-inv *3c burau-s2) ≡ id3
s2-inv-l = mat3-cong l11 l12 l13 l21 l22 l23 l31 l32 l33

-- ────────────────────────────────────────────────────────────────────
-- s1 逐点形不可能性（B0 骨架收口）：n=0 处 (s1*X) 的 a22 与 a32 同化为 X.a22(0)
-- 却须分别 = 1 / = 0 ⇒ 1 ≡ 0
-- ────────────────────────────────────────────────────────────────────
open import Cubical.Data.Int.Properties using (·AnnihilL; pos0+)

cf0-0 : cf0 (pos 0) ≡ pos 0
cf0-0 = refl

ann1 : ∀ u v → pos 0 · u + v ≡ v
ann1 u v = cong (_+ v) (·AnnihilL u) ∙ sym (pos0+ v)

ann2 : ∀ v w → v + pos 0 · w ≡ v
ann2 v w = cong (v +_) (·AnnihilL w)

s1-no-right-inv : ∀ (X : Mat3) → (burau-s1 *3 X) ≡ id3 → ⊥
s1-no-right-inv X e = 1≢0 ((sym eq22) ∙ eq32)
  where
    step-a = cong (λ z → z · Mat3.a12 X (pos 0) + Mat3.a22 X (pos 0)) cf0-0
    s1a22-0 = step-a ∙ ann1 (Mat3.a12 X (pos 0)) (Mat3.a22 X (pos 0))
    step-b = cong (λ z → (z · Mat3.a12 X (pos 0) + Mat3.a22 X (pos 0)) + z · Mat3.a32 X (pos 0)) cf0-0
    step-c = cong (_+ pos 0 · Mat3.a32 X (pos 0)) (ann1 (Mat3.a12 X (pos 0)) (Mat3.a22 X (pos 0)))
    s1a32-0 = step-b ∙ step-c ∙ ann2 (Mat3.a22 X (pos 0)) (Mat3.a32 X (pos 0))
    eq22 : Mat3.a22 X (pos 0) ≡ pos 1
    eq22 = sym s1a22-0 ∙ cong (λ M → Mat3.a22 M (pos 0)) e
    eq32 : Mat3.a22 X (pos 0) ≡ pos 0
    eq32 = sym s1a32-0 ∙ cong (λ M → Mat3.a32 M (pos 0)) e

-- ──── ⑦B′ 后续：卷积语义 braid-rel 重证（_PBRL 并入）────

-- | _PBRL（⑦B′ 后续件：卷积语义 braid-rel 重证）
--   *3 口径裁决定案（2026-10-11）：卷积形为正式表示层——本件在 _*3cv_（BurauInverse 的
--   窗口卷积矩阵乘，convN 窗 k∈{-1,0,1} 三项）下重证辫关系 σ₁σ₂σ₁ = σ₂σ₁σ₂。
--   范式：9 entry × 6-case 具名子句 funExt（braid-rel 逐点形模板）+ mat3-cong 装配。

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; funExt)

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
