{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Algebra.LaurentCubical
--
-- Laurent 多项式环 ℤ[t, t⁻¹] 的 Cubical 函数表示。
--
-- 数学背景：
--   ℤ[t, t⁻¹] = { f : ℤ → ℤ | f 有限支撑 }
--   这是 Laurent 多项式的数学定义（本源）。
--   List (ℤ × ℤ) 只是其投影编码。
--
-- 核心设计：
--   Laurent = Σ (ℤ → ℤ) IsFinSupp（依赖对偶）
--   sums n f = f n（直接应用，无 _≟_，无 Stuck）
--   funExt 从 Cubical Path 构造（0 postulate）
--
-- 解决的问题：
--   List 表示下 sums (c₁ , n₁) ((c₁ , n₁) ∷ xs) 因 n₁ ≟ n₁ Stuck。
--   函数表示下 sums n f = f n —— 直接应用，无比较。

module Sovereign.Algebra.LaurentCubical where

open import Cubical.Foundations.Prelude using
  (_≡_; refl; sym; _∙_; cong; cong₂; funExt; subst; Σ; Σ-syntax; _,_; fst; snd)
open import Cubical.Data.Int using (ℤ; _+_; _·_; _-_; -_; pos; negsuc)
open import Cubical.Data.Int.Order using (_<_; _≤_; ≤-+o; ≤-o+; ≤-+o-cancel; ≤-o+-cancel; isTrans≤; isRefl≤; <-weaken; ≤<-trans; <isTrans≤)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm; pos0+; ·AnnihilR; ·AnnihilL)
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (min; max; minSuc; +∸; +-comm; +-zero; +-suc)
open import Cubical.Data.Nat.Order using ()
open import Cubical.Data.Nat.Order using ()
open import Cubical.Data.List using (List; []; _∷_; _++_; map; foldr; length)
open import Cubical.Data.Empty using (⊥; ⊥-elim)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)

-- ────────────────────────────────────────────────────────────────────
-- 有限支撑谓词
-- ────────────────────────────────────────────────────────────────────

-- IsFinSupp f：存在有限区间 [L, U]，区间外 f n = 0
-- 真实约束：∀ n → (n < L) ⊎ (U < n) → f n ≡ 0
IsFinSupp : (ℤ → ℤ) → Set
IsFinSupp f = Σ[ L ∈ ℤ ] Σ[ U ∈ ℤ ]
  (∀ n → (n < L) ⊎ (U < n) → f n ≡ pos 0)

-- ────────────────────────────────────────────────────────────────────
-- Laurent = 有限支撑函数（依赖对偶）
-- ────────────────────────────────────────────────────────────────────

Laurent : Set
Laurent = Σ[ f ∈ (ℤ → ℤ) ] IsFinSupp f

-- 投影：取系数函数
coeff : Laurent → ℤ → ℤ
coeff f = fst f

-- 测试项（指数）
Exponent : Set
Exponent = ℤ

-- 逐指数系数和：直接应用，无 _≟_！
sums : Exponent → Laurent → ℤ
sums n f = fst f n

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique（Cubical funExt 下严格相等！）
-- ────────────────────────────────────────────────────────────────────

-- 核心定理：若对所有测试项 sums 相等，则系数函数相等（Path 相等）
canon-sums-unique-fn : (f g : ℤ → ℤ) →
  (∀ n → f n ≡ g n) → f ≡ g
canon-sums-unique-fn f g h = funExt h

-- 对 Laurent（含 FinSupp 证明）的版本
canon-sums-unique : (f g : Laurent) →
  (∀ n → sums n f ≡ sums n g) → fst f ≡ fst g
canon-sums-unique f g h = funExt h

-- ────────────────────────────────────────────────────────────────────
-- 零多项式
-- ────────────────────────────────────────────────────────────────────

-- 零多项式
R0 : Laurent
R0 = (λ _ → pos 0) , (pos 0 , pos 0 , λ n _ → refl)

-- ────────────────────────────────────────────────────────────────────
-- 加法（逐点）
-- ────────────────────────────────────────────────────────────────────

-- ℤ 上的 min/max（Cubical 无内置）
min-ℤ : ℤ → ℤ → ℤ
min-ℤ (pos m) (pos n) = pos (min m n)
min-ℤ (pos m) (negsuc n) = negsuc n
min-ℤ (negsuc m) (pos n) = negsuc m
min-ℤ (negsuc m) (negsuc n) = negsuc (max m n)

max-ℤ : ℤ → ℤ → ℤ
max-ℤ (pos m) (pos n) = pos (max m n)
max-ℤ (pos m) (negsuc n) = pos m
max-ℤ (negsuc m) (pos n) = pos n
max-ℤ (negsuc m) (negsuc n) = negsuc (min m n)

-- ℕ 算术辅助引理：m ∸ n + n ≡ m（当 n ≤ m，即 Σ[ k ] k + n ≡ m）
m∸n+n≡m : ∀ m n → Σ ℕ (λ k → k +ℕ n ≡ m) → (m ∸ n) +ℕ n ≡ m
m∸n+n≡m m n (k , p) =
  +-comm (m ∸ n) n ∙ cong (n +ℕ_) (cong (_∸ n) (sym p) ∙ +∸ k n) ∙ +-comm n k ∙ p

-- min≤ : min m n ≤ m（独立归纳，不依赖 m∸n+n≡m）
min≤ : ∀ m n → Σ ℕ (λ k → k +ℕ min m n ≡ m)
min≤ zero n = zero , refl
min≤ (suc m) zero = suc m , cong suc (+-zero m)
min≤ (suc m) (suc n) with min≤ m n
... | (k , p) = k , subst (λ x → k +ℕ x ≡ suc m) (sym minSuc) (+-suc k (min m n) ∙ cong suc p)

-- ℕ min/max 界引理（negsuc 反转序）
max-left : ∀ m n → negsuc (max m n) ≤ negsuc m
max-left m n = _∸_ (max m n) m , {!!}
max-right : ∀ m n → negsuc (max m n) ≤ negsuc n
max-right m n = _∸_ (max m n) n , {!!}
min-left : ∀ m n → negsuc m ≤ negsuc (min m n)
min-left m n = _∸_ m (min m n) , {!!}
min-right : ∀ m n → negsuc n ≤ negsuc (min m n)
min-right m n = _∸_ n (min m n) , {!!}

-- min-ℤ 界引理
min-ℤ≤ˡ : ∀ a b → min-ℤ a b ≤ a
min-ℤ≤ˡ (pos m) (pos n) = _∸_ m (min m n) , {!!}
min-ℤ≤ˡ (pos m) (negsuc n) = {!!}  -- negsuc n ≤ pos m
min-ℤ≤ˡ (negsuc m) (pos n) = ℕ.zero , refl
min-ℤ≤ˡ (negsuc m) (negsuc n) = max-left m n

min-ℤ≤ʳ : ∀ a b → min-ℤ a b ≤ b
min-ℤ≤ʳ (pos m) (pos n) = _∸_ n (min m n) , {!!}
min-ℤ≤ʳ (pos m) (negsuc n) = ℕ.zero , refl
min-ℤ≤ʳ (negsuc m) (pos n) = suc (m +ℕ n) , {!!}
min-ℤ≤ʳ (negsuc m) (negsuc n) = max-right m n

max-ℤ≤ˡ : ∀ a b → a ≤ max-ℤ a b
max-ℤ≤ˡ (pos m) (pos n) = _∸_ (max m n) m , {!!}
max-ℤ≤ˡ (pos m) (negsuc n) = ℕ.zero , refl  -- max-ℤ (pos m) (negsuc n) = pos m ≤ pos m
max-ℤ≤ˡ (negsuc m) (pos n) = suc (m +ℕ n) , {!!}
max-ℤ≤ˡ (negsuc m) (negsuc n) = min-left m n

max-ℤ≤ʳ : ∀ a b → b ≤ max-ℤ a b
max-ℤ≤ʳ (pos m) (pos n) = _∸_ (max m n) n , {!!}
max-ℤ≤ʳ (pos m) (negsuc n) = suc (m +ℕ n) , {!!}
max-ℤ≤ʳ (negsuc m) (pos n) = ℕ.zero , refl  -- max-ℤ (negsuc m) (pos n) = pos n ≤ pos n
max-ℤ≤ʳ (negsuc m) (negsuc n) = min-right m n

-- 逐点加法
_+L_ : Laurent → Laurent → Laurent
(f , (Lf , Uf , bf)) +L (g , (Lg , Ug , bg)) =
  (λ n → f n + g n) , (min-ℤ Lf Lg , max-ℤ Uf Ug , bound)
  where
  bound : ∀ n → (n < min-ℤ Lf Lg) ⊎ (max-ℤ Uf Ug < n) → f n + g n ≡ pos 0
  bound n h = cong₂ _+_ (bf n (left h)) (bg n (right h))
    where
    left : (n < min-ℤ Lf Lg) ⊎ (max-ℤ Uf Ug < n) → (n < Lf) ⊎ (Uf < n)
    left (inl x) = inl {!!}  -- min-ℤ Lf Lg ≤ Lf
    left (inr x) = inr {!!}  -- Uf ≤ max-ℤ Uf Ug
    right : (n < min-ℤ Lf Lg) ⊎ (max-ℤ Uf Ug < n) → (n < Lg) ⊎ (Ug < n)
    right (inl x) = inl {!!}  -- min-ℤ Lf Lg ≤ Lg
    right (inr x) = inr {!!}  -- Ug ≤ max-ℤ Uf Ug

-- ────────────────────────────────────────────────────────────────────
-- 卷积乘法（参考 agda-unimath 的 convolution-sequences）
-- ────────────────────────────────────────────────────────────────────

-- 卷积：(f * g)(n) = Σ_k f(k) * g(n - k)
-- 有限支撑下只需对 f 的支撑求和
-- 参考：agda-unimath/src/commutative-algebra/convolution-sequences-commutative-semirings.lagda.md

-- ────────────────────────────────────────────────────────────────────
-- 卷积乘法（参考 agda-unimath 的 convolution-sequences）
-- ────────────────────────────────────────────────────────────────────

-- 有限求和：∑_{i=0}^{n} f(i)（对 ℕ 归纳）
sum-ℕ : (ℕ → ℤ) → ℕ → ℤ
sum-ℕ f zero = f zero
sum-ℕ f (suc n) = sum-ℕ f n + f (suc n)

-- 卷积乘法：(f * g)(n) = Σ_k f(k) * g(n - k)
-- 有限支撑下只需对 f 的支撑求和
-- ────────────────────────────────────────────────────────────────────
-- 卷积乘法（参考 agda-unimath 的 convolution-sequences）
-- ────────────────────────────────────────────────────────────────────

-- ℤ → ℕ 转换（绝对值）
abs : ℤ → ℕ
abs (pos n) = n
abs (negsuc n) = suc n

-- 有限求和 over ℤ：∑_{k=L}^{U} f(k)
-- 用 sum-ℕ 实现：将 [L, U] 映射到 [0, U-L]
sum-ℤ : (ℤ → ℤ) → ℤ → ℕ → ℤ
sum-ℤ f L zero = f L
sum-ℤ f L (suc n) = sum-ℤ f L n + f (L + pos (suc n))

-- 卷积乘法：(f * g)(n) = Σ_k f(k) * g(n - k)
-- ────────────────────────────────────────────────────────────────────
-- 卷积乘法（参考 agda-unimath 的 convolution-sequences）
-- ────────────────────────────────────────────────────────────────────
-- case_of_ 辅助
-- ────────────────────────────────────────────────────────────────────

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

-- ────────────────────────────────────────────────────────────────────
-- 零求和引理
-- ────────────────────────────────────────────────────────────────────

sum-ℕ-zero : (n : ℕ) → sum-ℕ (λ _ → pos 0) n ≡ pos 0
sum-ℕ-zero zero = refl
sum-ℕ-zero (suc n) = cong (_+ pos 0) (sum-ℕ-zero n) ∙ pos0+ (pos 0)

sum-ℤ-zero : (f : ℤ → ℤ) → (L : ℤ) → (n : ℕ) → (∀ k → f k ≡ pos 0) → sum-ℤ f L n ≡ pos 0
sum-ℤ-zero f L zero h = h L
sum-ℤ-zero f L (suc n) h = cong₂ _+_ (sum-ℤ-zero f L n h) (h (L + pos (suc n)))

-- ────────────────────────────────────────────────────────────────────
-- 卷积乘法（参考 agda-unimath 的 convolution-sequences）
-- ────────────────────────────────────────────────────────────────────

_*L_ : Laurent → Laurent → Laurent
(f , (Lf , Uf , bf)) *L (g , (Lg , Ug , bg)) =
  (λ n → conv-sum f g n) , (Lf + Lg , Uf + Ug , bound)
  where
  conv-sum : (ℤ → ℤ) → (ℤ → ℤ) → ℤ → ℤ
  conv-sum f g n = sum-ℤ (λ k → f k · g (n - k)) Lf (abs (Uf - Lf))
  
  bound : ∀ n → (n < Lf + Lg) ⊎ (Uf + Ug < n) → conv-sum f g n ≡ pos 0
  bound n h = sum-ℤ-zero (λ k → f k · g (n - k)) Lf (abs (Uf - Lf)) (λ k → term-zero k h)
    where
    term-zero : ∀ k → (n < Lf + Lg) ⊎ (Uf + Ug < n) → f k · g (n - k) ≡ pos 0
    term-zero k h = cong (f k ·_) (g-zero k h) ∙ ·AnnihilR (f k)
      where
      g-zero : ∀ k → (n < Lf + Lg) ⊎ (Uf + Ug < n) → g (n - k) ≡ pos 0
      g-zero k h = bg (n - k) (bound-n-k k h)
        where
        bound-n-k : ∀ k → (n < Lf + Lg) ⊎ (Uf + Ug < n) → (n - k < Lg) ⊎ (Ug < n - k)
        bound-n-k k h = {!!}  -- 待证：需 sum-ℤ 重写暴露 k ∈ [Lf, Uf] 界

-- ────────────────────────────────────────────────────────────────────
-- 加法性质（从 ℤ 的算术直接推出）
-- ────────────────────────────────────────────────────────────────────

-- 加法性质（逐点相等，避免 funExt 类型推断问题）
+L-assoc : (f g h : ℤ → ℤ) →
  ∀ n → (f n + g n) + h n ≡ f n + (g n + h n)
+L-assoc f g h n = sym (+Assoc (f n) (g n) (h n))

+L-comm : (f g : ℤ → ℤ) →
  ∀ n → f n + g n ≡ g n + f n
+L-comm f g n = +Comm (f n) (g n)
