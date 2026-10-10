{-# OPTIONS --cubical --guardedness #-}

-- | _PAW（⑦A 原子：A2 窗口等价（★）+ A4 零因子卷积）
--
-- A2：两窗口同含支撑 ⇒ 和相等（修正版 Covers——任务书版右零区差一，已报父代理）
-- A4：支撑空 ⇒ 卷积 = 0
module _PAW where

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; _∙_; cong; subst; _,_)
open import Cubical.Data.Int using (ℤ; pos; sucℤ; _+_; _-_; _·_; _+pos_)
open import Cubical.Data.Int.Order using (_≤_; ≤-refl) renaming (_<_ to _<ℤ_)
open import Cubical.Data.Int.Properties using (·AnnihilL; ·AnnihilR; sucℤ+; +Comm)
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-comm; +-suc)
open import Cubical.Data.Nat.Order using () renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Sovereign.Algebra.LaurentRingLaws using
  (sum-ℤ-grow-left; sum-ℤ-grow-right; zero-r)
open import Sovereign.Algebra.LaurentCubical using
  (sum-ℤ; sum-ℤ-zero; Laurent; coeff; sums; _*L_; mono-coeff; abs; min-ℤ; min-ℤ≤ˡ; min-ℤ≤ʳ)
open import Sovereign.Algebra.ProbeArith using (pos-split; ≤-witness; ≤-eq)

-- ────────────────────────────────────────────────────────────────────
-- Covers（修正版）：窗口 [L, L+n] 外项为零；右零区 L +pos n <ℤ i（= i > L+n）
--   任务书版写 L +pos suc n，漏 i = L+n+1，反例 t = δ_{L+n+1}（已报父代理）
-- ────────────────────────────────────────────────────────────────────
Covers : (ℤ → ℤ) → ℤ → ℕ → Set
Covers t L n = ∀ i → (i <ℤ L) ⊎ (L +pos n <ℤ i) → t i ≡ pos 0

-- ────────────────────────────────────────────────────────────────────
-- 桥族（全具名；∙ 链 ≤3）
-- ────────────────────────────────────────────────────────────────────

-- +pos 递归式（Base）：z +pos suc j = sucℤ (z +pos j) ⇒ 此桥为 refl
sucℤ-+pos : ∀ z j → sucℤ (z +pos j) ≡ z +pos suc j
sucℤ-+pos z j = refl

-- 右加 sucℤ 交换：z + sucℤ x ≡ sucℤ (z + x)（+Comm + sucℤ+ 组合）
+sucℤ-swap : ∀ z x → z + sucℤ x ≡ sucℤ (z + x)
+sucℤ-swap z x = +Comm z (sucℤ x) ∙ sym (sucℤ+ x z) ∙ cong sucℤ (+Comm x z)

-- +pos 形与 + pos 形桥：z +pos m ≡ z + pos m（对 m 归纳）
+pos-≡+ : ∀ z m → z +pos m ≡ z + pos m
+pos-≡+ z zero = sym (zero-r z)
+pos-≡+ z (suc m) = cong sucℤ (+pos-≡+ z m) ∙ sym (+sucℤ-swap z (pos m))

-- +pos 在 ℕ 参上单调（见证复用）
+pos-mono-≤ : ∀ z a b → a ≤ℕ b → (z +pos a) ≤ (z +pos b)
+pos-mono-≤ z a b (k , p) = k , (sym (pos-split z a k) ∙ cong (z +pos_) (+-comm a k) ∙ cong (z +pos_) p)

-- ℕ 级见证：suc K ≤ suc (K +ℕ j)（见证 j）
suc-K-≤ : ∀ K j → suc K ≤ℕ suc (K +ℕ j)
suc-K-≤ K j = j , (+-suc j K ∙ cong suc (+-comm j K))

-- 左零区条件转化：Covers ⇒ 扩窗起点段为零
cover-left : ∀ (t : ℤ → ℤ) L n (MIN : ℤ) k → MIN +pos k ≡ L → Covers t L n
           → ∀ j → j <ℕ k → t (MIN +pos j) ≡ pos 0
cover-left t L n MIN k eL cov j jlt = cov (MIN +pos j) (inl left<)
  where
  left-base : MIN +pos suc j ≤ MIN +pos k
  left-base = +pos-mono-≤ MIN (suc j) k jlt
  left-mid : sucℤ (MIN +pos j) ≤ MIN +pos k
  left-mid = subst (_≤ MIN +pos k) (sucℤ-+pos MIN j) left-base
  left< : sucℤ (MIN +pos j) ≤ L
  left< = subst (sucℤ (MIN +pos j) ≤_) eL left-mid

-- 右零区条件转化（出口为 grow-right 所需的 + pos 形）：对任意 j 成立
cover-right : ∀ (t : ℤ → ℤ) L n (MIN : ℤ) K → MIN +pos K ≡ L +pos n → Covers t L n
            → ∀ j → t (MIN + pos (suc (K +ℕ j))) ≡ pos 0
cover-right t L n MIN K e cov j = subst (λ z → t z ≡ pos 0) (+pos-≡+ MIN (suc (K +ℕ j))) core
  where
  right-base : MIN +pos suc K ≤ MIN +pos suc (K +ℕ j)
  right-base = +pos-mono-≤ MIN (suc K) (suc (K +ℕ j)) (suc-K-≤ K j)
  right-mid : sucℤ (MIN +pos K) ≤ MIN +pos suc (K +ℕ j)
  right-mid = subst (_≤ MIN +pos suc (K +ℕ j)) (sucℤ-+pos MIN K) right-base
  right> : L +pos n <ℤ MIN +pos suc (K +ℕ j)
  right> = subst (_≤ MIN +pos suc (K +ℕ j)) (cong sucℤ e) right-mid
  core : t (MIN +pos suc (K +ℕ j)) ≡ pos 0
  core = cov (MIN +pos suc (K +ℕ j)) (inr right>)

-- ────────────────────────────────────────────────────────────────────
-- A2 主件：两窗口同含支撑 ⇒ 和相等
--   路线：双侧左扩到公共起点 MIN = min-ℤ L L'，再各右扩到 K1+K2 与 K2+K1（+ -comm 收口）
-- ────────────────────────────────────────────────────────────────────

sum-ℤ-window-eq : ∀ (t : ℤ → ℤ) L n L' n' → Covers t L n → Covers t L' n'
                → sum-ℤ t L n ≡ sum-ℤ t L' n'
sum-ℤ-window-eq t L n L' n' cov cov' = side1 ∙ cross ∙ sym side2
  where
  MIN : ℤ
  MIN = min-ℤ L L'
  kL : ℕ
  kL = ≤-witness (min-ℤ≤ˡ L L')
  eL : MIN +pos kL ≡ L
  eL = ≤-eq (min-ℤ≤ˡ L L')
  kL' : ℕ
  kL' = ≤-witness (min-ℤ≤ʳ L L')
  eL' : MIN +pos kL' ≡ L'
  eL' = ≤-eq (min-ℤ≤ʳ L L')
  K1 : ℕ
  K1 = kL +ℕ n
  K2 : ℕ
  K2 = kL' +ℕ n'
  e1 : MIN +pos K1 ≡ L +pos n
  e1 = pos-split MIN kL n ∙ cong (_+pos n) eL
  e2 : MIN +pos K2 ≡ L' +pos n'
  e2 = pos-split MIN kL' n' ∙ cong (_+pos n') eL'
  step1L : sum-ℤ t L n ≡ sum-ℤ t MIN K1
  step1L = sym (cong (λ z → sum-ℤ t z n) eL)
         ∙ sym (sum-ℤ-grow-left t MIN n kL (cover-left t L n MIN kL eL cov))
  step1R : sum-ℤ t MIN K1 ≡ sum-ℤ t MIN (K1 +ℕ K2)
  step1R = sym (sum-ℤ-grow-right t MIN K1 K2 (λ j _ → cover-right t L n MIN K1 e1 cov j))
  side1 : sum-ℤ t L n ≡ sum-ℤ t MIN (K1 +ℕ K2)
  side1 = step1L ∙ step1R
  step2L : sum-ℤ t L' n' ≡ sum-ℤ t MIN K2
  step2L = sym (cong (λ z → sum-ℤ t z n') eL')
         ∙ sym (sum-ℤ-grow-left t MIN n' kL' (cover-left t L' n' MIN kL' eL' cov'))
  step2R : sum-ℤ t MIN K2 ≡ sum-ℤ t MIN (K2 +ℕ K1)
  step2R = sym (sum-ℤ-grow-right t MIN K2 K1 (λ j _ → cover-right t L' n' MIN K2 e2 cov' j))
  side2 : sum-ℤ t L' n' ≡ sum-ℤ t MIN (K2 +ℕ K1)
  side2 = step2L ∙ step2R
  cross : sum-ℤ t MIN (K1 +ℕ K2) ≡ sum-ℤ t MIN (K2 +ℕ K1)
  cross = cong (sum-ℤ t MIN) (+-comm K1 K2)

-- ────────────────────────────────────────────────────────────────────
-- A4：零因子卷积（支撑空 ⇒ 卷积 = 0）
-- ────────────────────────────────────────────────────────────────────

conv-zeroˡ : ∀ (f g : Laurent) k → (∀ i → coeff f i ≡ pos 0) → sums k (f *L g) ≡ pos 0
conv-zeroˡ (f , Lf , Uf , bf) (g , _) k h =
  sum-ℤ-zero (λ i → f i · g (k - i)) Lf (abs (Uf - Lf))
    (λ i → cong (_· g (k - i)) (h i) ∙ ·AnnihilL (g (k - i)))

conv-zeroʳ : ∀ (f g : Laurent) k → (∀ i → coeff g i ≡ pos 0) → sums k (f *L g) ≡ pos 0
conv-zeroʳ (f , Lf , Uf , bf) (g , _) k h =
  sum-ℤ-zero (λ i → f i · g (k - i)) Lf (abs (Uf - Lf))
    (λ i → cong (f i ·_) (h (k - i)) ∙ ·AnnihilR (f i))

-- ────────────────────────────────────────────────────────────────────
-- 交叉核对（refl 级小件）
-- ────────────────────────────────────────────────────────────────────

zero-fn : ℤ → ℤ
zero-fn _ = pos 0

zero-covers : ∀ L n → Covers zero-fn L n
zero-covers L n i _ = refl

-- 核对 1：主件端到端（零函数两窗口 [0,0] 与 [5,8]）
test-window-eq : sum-ℤ zero-fn (pos 0) 0 ≡ sum-ℤ zero-fn (pos 5) 3
test-window-eq = sum-ℤ-window-eq zero-fn (pos 0) 0 (pos 5) 3
                   (zero-covers (pos 0) 0) (zero-covers (pos 5) 3)

-- 核对 2：单点支撑 mono 两窗口偏移（refl 级计算：mono (pos 1) (pos 2)）
test-mono : sum-ℤ (mono-coeff (pos 1) (pos 2)) (pos 1) 3
          ≡ sum-ℤ (mono-coeff (pos 1) (pos 2)) (pos 0) 8
test-mono = refl
