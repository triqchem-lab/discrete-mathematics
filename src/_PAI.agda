{-# OPTIONS --cubical --guardedness #-}

-- | _PAI（⑦A · *assoc 装配链第 4 步：逐点内层等式 A5-inner-eq）
--
-- 装配链：sum-ℤ-·r → sym ·Assoc → sum-ℤ-swap →【本件点化】→ sum-ℤ-·l → sum-ℤ-reindex → ★window-eq
-- 本件形态（未来态锚定——产出即第 5/6 步入口形）：
--   LHS = Σᵢ∈W f j · (g (i-j) · h (k-i))   （swap 后的内层和，W = 任意窗口 (L,n)）
--   RHS = f j · Σₗ g l · h ((k-j) - l)     （·l 拉出 f j + reindex l = i - j，窗口平移 L - j）
-- 分支（bf-j）：j ∉ [Lf,Uf] → f j ≡ 0 → 两边 0·_-形（供 ★window-eq 扩窗归零用）
module _PAI where

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; cong)
open import Cubical.Data.Int using (ℤ; pos; _+_; _-_; _·_)
open import Cubical.Data.Int.Order using (_<_; Trichotomy; lt; eq; gt)
open import Cubical.Data.Int.Properties using (·AnnihilL)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Sovereign.Algebra.ProbeArith using (triℤ)
open import Sovereign.Algebra.LaurentCubical using (sum-ℤ; sum-ℤ-zero)
open import Sovereign.Algebra.LaurentRingLaws using (sum-ℤ-·l; sum-ℤ-cong; sum-ℤ-reindex; shuffle)

-- ────────────────────────────────────────────────────────────────────
-- 1. shuffle 点化（summand 级）：h 的指数重引
--    shuffle k i j : (k - j) - (i - j) ≡ k - i  ⇒  h (k - i) ≡ h ((k - j) - (i - j))
-- ────────────────────────────────────────────────────────────────────

shuffle-point : ∀ (g h : ℤ → ℤ) (k i j : ℤ)
  → g (i - j) · h (k - i) ≡ g (i - j) · h ((k - j) - (i - j))
shuffle-point g h k i j = cong (g (i - j) ·_) (cong h (sym (shuffle k i j)))

-- ────────────────────────────────────────────────────────────────────
-- 2. 内核重引（g/h 件，无 f）：Σᵢ g(i-j)·h(k-i) ≡ Σₗ g l·h((k-j)-l)（窗口平移 L - j）
-- ────────────────────────────────────────────────────────────────────

inner-core : ∀ (g h : ℤ → ℤ) (k j L : ℤ) (n : ℕ)
  → sum-ℤ (λ i → g (i - j) · h (k - i)) L n
  ≡ sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n
inner-core g h k j L n =
    sum-ℤ-cong (λ i → g (i - j) · h (k - i))
               (λ i → g (i - j) · h ((k - j) - (i - j))) L n
               (λ i → shuffle-point g h k i j)
  ∙ sum-ℤ-reindex (λ l → g l · h ((k - j) - l)) L n j

-- ────────────────────────────────────────────────────────────────────
-- 3. 内支主件（任意 j 成立）：·l 拉出 f j + 内核重引
-- ────────────────────────────────────────────────────────────────────

inner-main : ∀ (f g h : ℤ → ℤ) (k j L : ℤ) (n : ℕ)
  → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) L n
  ≡ f j · sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n
inner-main f g h k j L n =
    sum-ℤ-·l (f j) (λ i → g (i - j) · h (k - i)) L n
  ∙ cong (f j ·_) (inner-core g h k j L n)

-- ────────────────────────────────────────────────────────────────────
-- 4. 外支归零件（f j ≡ 0 → 两边 0·_-形）
-- ────────────────────────────────────────────────────────────────────

inner-zero-lhs : ∀ (f g h : ℤ → ℤ) (k j L : ℤ) (n : ℕ) → f j ≡ pos 0
  → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) L n ≡ pos 0
inner-zero-lhs f g h k j L n fj0 =
  sum-ℤ-zero (λ i → f j · (g (i - j) · h (k - i))) L n
    (λ i → cong (_· (g (i - j) · h (k - i))) fj0 ∙ ·AnnihilL (g (i - j) · h (k - i)))

inner-zero-rhs : ∀ (f g h : ℤ → ℤ) (k j L : ℤ) (n : ℕ) → f j ≡ pos 0
  → f j · sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n ≡ pos 0
inner-zero-rhs f g h k j L n fj0 =
  cong (_· sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n) fj0
  ∙ ·AnnihilL (sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n)

zero-branch : ∀ (f g h : ℤ → ℤ) (k j L : ℤ) (n : ℕ) → f j ≡ pos 0
  → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) L n
  ≡ f j · sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n
zero-branch f g h k j L n fj0 =
    inner-zero-lhs f g h k j L n fj0
  ∙ sym (inner-zero-rhs f g h k j L n fj0)

-- ────────────────────────────────────────────────────────────────────
-- 5. A5-inner-eq（tri 分派：内支 = inner-main / 外支 = zero-branch）
--    bf = f 的有限支撑证人（IsFinSupp 形状：j ∉ [Lf,Uf] → f j ≡ 0）
-- ────────────────────────────────────────────────────────────────────

inner-eq : ∀ (f g h : ℤ → ℤ) (Lf Uf : ℤ)
         (bf : ∀ n → (n < Lf) ⊎ (Uf < n) → f n ≡ pos 0)
         (k j L : ℤ) (n : ℕ)
  → sum-ℤ (λ i → f j · (g (i - j) · h (k - i))) L n
  ≡ f j · sum-ℤ (λ l → g l · h ((k - j) - l)) (L - j) n
inner-eq f g h Lf Uf bf k j L n with triℤ j Lf | triℤ Uf j
... | lt x | _     = zero-branch f g h k j L n (bf j (inl x))
... | eq e | lt y  = zero-branch f g h k j L n (bf j (inr y))
... | eq e | eq e' = inner-main f g h k j L n
... | eq e | gt y  = inner-main f g h k j L n
... | gt x | lt y  = zero-branch f g h k j L n (bf j (inr y))
... | gt x | eq e' = inner-main f g h k j L n
... | gt x | gt y  = inner-main f g h k j L n

-- ────────────────────────────────────────────────────────────────────
-- 6. 验证点（②）：内支小例（refl 交叉）+ 外支小例（归零交叉）
-- ────────────────────────────────────────────────────────────────────

-- 内支：全 1 系数、窗口 (pos 0, 1)、k = 0、j = 0：1·(1·1)+1·(1·1) = 1·(1·1+1·1) = 2
check-in : sum-ℤ (λ i → pos 1 · (pos 1 · pos 1)) (pos 0) 1
         ≡ pos 1 · sum-ℤ (λ l → pos 1 · pos 1) (pos 0 - pos 0) 1
check-in = refl

-- 外支：f j = 0 → 两边 0·_-形，各归零
check-out-lhs : sum-ℤ (λ i → pos 0 · (pos 1 · pos 1)) (pos 0) 1 ≡ pos 0
check-out-lhs = refl

check-out-rhs : pos 0 · sum-ℤ (λ l → pos 1 · pos 1) (pos 0 - pos 0) 1 ≡ pos 0
check-out-rhs = refl

check-out : sum-ℤ (λ i → pos 0 · (pos 1 · pos 1)) (pos 0) 1
          ≡ pos 0 · sum-ℤ (λ l → pos 1 · pos 1) (pos 0 - pos 0) 1
check-out = inner-eq (λ _ → pos 0) (λ _ → pos 1) (λ _ → pos 1) (pos 0) (pos 0)
                    (λ n _ → refl) (pos 0) (pos 0) (pos 0) 1
