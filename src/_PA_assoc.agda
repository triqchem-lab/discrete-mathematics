{-# OPTIONS --cubical --guardedness #-}

-- | _PA_assoc（⑦A 子件④探针：卷积结合律——sum-ℤ 双和交换核心件）
--
-- 核心：sum-ℤ-split（和分配）+ sum-ℤ-swap（双和交换/interchange）+ · 分配两形
module _PA_assoc where

open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int using (ℤ; _+_; _-_; _·_; -_; pos; negsuc)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int.Properties using (+Comm; +Assoc; ·DistR+; ·DistL+; minusPlus; pos0+; -Cancel'; -Involutive; -Dist+)
open import Sovereign.Algebra.LaurentCubical using (sum-ℤ)

-- 三元交换：b + (c + d) ≡ c + (b + d)
+swap3 : ∀ b c d → b + (c + d) ≡ c + (b + d)
+swap3 b c d = +Assoc b c d ∙ cong (_+ d) (+Comm b c) ∙ sym (+Assoc c b d)

-- 四元交叉：(a + b) + (c + d) ≡ (a + c) + (b + d)
+interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+interchange a b c d = sym (+Assoc a b (c + d)) ∙ cong (a +_) (+swap3 b c d) ∙ +Assoc a c (b + d)

-- 和分配：Σ (f + g) ≡ Σ f + Σ g
sum-ℤ-split : ∀ (f g : ℤ → ℤ) (L : ℤ) (n : ℕ) →
  sum-ℤ (λ i → f i + g i) L n ≡ sum-ℤ f L n + sum-ℤ g L n
sum-ℤ-split f g L zero = refl
sum-ℤ-split f g L (suc n) =
  cong (_+ (f (L + pos (suc n)) + g (L + pos (suc n)))) (sum-ℤ-split f g L n)
  ∙ +interchange (sum-ℤ f L n) (sum-ℤ g L n) (f (L + pos (suc n))) (g (L + pos (suc n)))

-- 双和交换（interchange）：Σᵢ Σⱼ F i j ≡ Σⱼ Σᵢ F i j
sum-ℤ-swap : ∀ (F : ℤ → ℤ → ℤ) (L₁ : ℤ) (n : ℕ) (L₂ : ℤ) (m : ℕ) →
  sum-ℤ (λ i → sum-ℤ (F i) L₂ m) L₁ n ≡ sum-ℤ (λ j → sum-ℤ (λ i → F i j) L₁ n) L₂ m
sum-ℤ-swap F L₁ zero L₂ m = refl
sum-ℤ-swap F L₁ (suc n) L₂ m =
  cong (_+ sum-ℤ (F (L₁ + pos (suc n))) L₂ m) (sum-ℤ-swap F L₁ n L₂ m)
  ∙ sym (sum-ℤ-split (λ j → sum-ℤ (λ i → F i j) L₁ n) (F (L₁ + pos (suc n))) L₂ m)

-- 右乘分配：(Σ φ) · c ≡ Σ (λ i → φ i · c)
sum-ℤ-·r : ∀ (φ : ℤ → ℤ) (L : ℤ) (n : ℕ) (c : ℤ) →
  sum-ℤ φ L n · c ≡ sum-ℤ (λ i → φ i · c) L n
sum-ℤ-·r φ L zero c = refl
sum-ℤ-·r φ L (suc n) c =
  ·DistL+ (sum-ℤ φ L n) (φ (L + pos (suc n))) c
  ∙ cong (_+ φ (L + pos (suc n)) · c) (sum-ℤ-·r φ L n c)

-- 左乘分配：Σ (λ i → c · φ i) ≡ c · (Σ φ)
sum-ℤ-·l : ∀ (c : ℤ) (φ : ℤ → ℤ) (L : ℤ) (n : ℕ) →
  sum-ℤ (λ i → c · φ i) L n ≡ c · sum-ℤ φ L n
sum-ℤ-·l c φ L zero = refl
sum-ℤ-·l c φ L (suc n) =
  cong (_+ c · φ (L + pos (suc n))) (sum-ℤ-·l c φ L n)
  ∙ sym (·DistR+ c (sum-ℤ φ L n) (φ (L + pos (suc n))))

-- ────────────────────────────────────────────────────────────────────
-- 指数移位件（窗口重引基础设施）
-- ────────────────────────────────────────────────────────────────────

-- 移位交换：(L + s) - j ≡ (L - j) + s
+-shift : ∀ L j s → (L + s) - j ≡ (L - j) + s
+-shift L j s = sym (+Assoc L s (- j)) ∙ cong (L +_) (+Comm s (- j)) ∙ +Assoc L (- j) s

-- 抵消移位：(k - i) + (i - j) ≡ k - j
-shift : ∀ k i j → (k - i) + (i - j) ≡ k - j
-shift k i j = +Assoc (k - i) i (- j) ∙ cong (_+ (- j)) (minusPlus i k)

-- 右零：x + pos 0 ≡ x
zero-r : ∀ x → x + pos 0 ≡ x
zero-r (pos n) = refl
zero-r (negsuc n) = refl

-- 尾部相消：(- i) + (- j + j) ≡ - i
inner-kill : ∀ i j → (- i) + (- j + j) ≡ - i
inner-kill i j = cong ((- i) +_) (-Cancel' j) ∙ zero-r (- i)

-- 内层三元交换（命名拆分——击败嵌套精化）
inner-swap : ∀ i j → (- j) + ((- i) + j) ≡ (- i) + (- j + j)
inner-swap i j = +swap3 (- j) (- i) j

-- 负差展开：- (i - j) ≡ (- i) + j
neg-shuffle : ∀ i j → - (i - j) ≡ (- i) + j
neg-shuffle i j = -Dist+ i (- j) ∙ cong ((- i) +_) (-Involutive j)

-- 重引恒等式：(k - j) - (i - j) ≡ k - i
shuffle : ∀ k i j → (k - j) - (i - j) ≡ k - i
shuffle k i j =
  cong ((k + - j) +_) (neg-shuffle i j)
  ∙ sym (+Assoc k (- j) ((- i) + j))
  ∙ cong (k +_) (inner-swap i j ∙ inner-kill i j)

-- 逐点同余：Σ 逐点等则和等
sum-ℤ-cong : ∀ (φ ψ : ℤ → ℤ) (L : ℤ) (n : ℕ) → (∀ i → φ i ≡ ψ i) →
  sum-ℤ φ L n ≡ sum-ℤ ψ L n
sum-ℤ-cong φ ψ L zero h = h L
sum-ℤ-cong φ ψ L (suc n) h =
  cong (_+ φ (L + pos (suc n))) (sum-ℤ-cong φ ψ L n h) ∙ cong (sum-ℤ ψ L n +_) (h (L + pos (suc n)))

-- 窗口平移重引：Σᵢ ψ(i - j) 在 [L, L+n] ≡ Σ_l ψ l 在 [L - j, (L - j) + n]
sum-ℤ-reindex : ∀ (ψ : ℤ → ℤ) (L : ℤ) (n : ℕ) (j : ℤ) →
  sum-ℤ (λ i → ψ (i - j)) L n ≡ sum-ℤ ψ (L - j) n
sum-ℤ-reindex ψ L zero j = refl
sum-ℤ-reindex ψ L (suc n) j =
  cong (_+ ψ ((L + pos (suc n)) - j)) (sum-ℤ-reindex ψ L n j)
  ∙ cong (sum-ℤ ψ (L - j) n +_) (cong ψ (+-shift L j (pos (suc n))))
