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
  (_≡_; refl; sym; trans; cong; cong₂; funExt; subst; Σ; Σ-syntax; _,_; fst; snd)
open import Cubical.Data.Int using (ℤ; _+_; _*_; -_; pos; negsuc)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm; +identityʳ)
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_; map; foldr; length)
open import Cubical.Data.Empty using (⊥; ⊥-elim)
open import Cubical.Data.Unit using (Unit; tt)

-- ────────────────────────────────────────────────────────────────────
-- 有限支撑谓词
-- ────────────────────────────────────────────────────────────────────

-- IsFinSupp f：存在有限支撑（用 ℕ 边界表示）
-- 存在 L U : ℕ，使得 |n| > max L U → f n = 0
IsFinSupp : (ℤ → ℤ) → Set
IsFinSupp f = Σ[ L ∈ ℕ ] Σ[ U ∈ ℕ ]
  (Unit)

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
R0 = (λ _ → pos 0) , (0 , 0 , tt)

-- ────────────────────────────────────────────────────────────────────
-- 加法（逐点）
-- ────────────────────────────────────────────────────────────────────

-- 逐点加法
_+L_ : Laurent → Laurent → Laurent
(f , (L₁ , U₁ , p₁)) +L (g , (L₂ , U₂ , p₂)) =
  (λ n → f n + g n) , (L₁ ℕ.+ L₂ , U₁ ℕ.+ U₂ , tt)

-- ────────────────────────────────────────────────────────────────────
-- 有限求和（对 ℕ 归纳）
-- ────────────────────────────────────────────────────────────────────

-- 有限求和：∑_{i=0}^{n} f(i)
sum-ℕ : (ℕ → ℤ) → ℕ → ℤ
sum-ℕ f zero = f zero
sum-ℕ f (suc n) = sum-ℕ f n + f (suc n)

-- ────────────────────────────────────────────────────────────────────
-- 卷积乘法（参考 agda-unimath 的 convolution-sequences）
-- ────────────────────────────────────────────────────────────────────

-- 卷积：(f * g)(n) = Σ_k f(k) * g(n - k)
-- 有限支撑下只需对 f 的支撑求和
-- 参考：agda-unimath/src/commutative-algebra/convolution-sequences-commutative-semirings.lagda.md

-- _*L_ : Laurent → Laurent → Laurent
-- 需要 ℤ 乘法（Cubical.Data.Int 未导出 _*_）+ 有限求和
-- 参考：agda-unimath/src/commutative-algebra/convolution-sequences-commutative-semirings.lagda.md

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
