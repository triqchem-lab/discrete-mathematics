{-# OPTIONS --cubical --guardedness #-}

-- | _PBI2（⑦B′ 子件 B4：σ₂ 块逆律——陈述体检 + 卷积修正版双交付）
--
-- ⚠ 任务书陈述体检：`(burau-s2 *3 s2-inv) ≡ id3` 按 _*3_（BurauCubical 的逐点系数乘法）为**假**：
--   n=0 处 burau-s2 系数阵 = [[1,0,0],[1,0,0],[0,0,1]]，前两行相同 ⇒ 乘积前两行恒同 ⇒ 永不等于 id3。
--   本件双交付：① 不可能性证书 no-right-inv / no-left-inv（statement_wrong 证据）；
--   ② 卷积语义（Laurent 环）修正版：_*3c_ 矩阵乘 + s2-inv + s2-inv-r / s2-inv-l（真逆律）。
-- 一般层 t·t⁻¹=1 与 mono-conv 在 Sovereign.Algebra.LaurentRingLaws（t-tinv/tinv-t/mono-conv），
-- 本件为其 δ 具体例（refl 级，不重证泛形）。
module _PBI2 where

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
