{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LaurentFn
--
-- Laurent 多项式环 ℤ[t, t⁻¹] 的函数表示。
--
-- 数学背景：
--   Laurent 多项式可表示为有限支撑函数 f : ℤ → ℤ，
--   其中 f n = n 次项的系数。乘法为卷积，加法为逐点加法。
--
-- 核心设计：
--   `sums u f = f (proj₂ u)` —— 直接应用，无 `_≟_`，无 Stuck 项！
--   `canon-sums-unique` 在函数表示下变为平凡：
--     `∀ u → f (proj₂ u) ≡ g (proj₂ u)` 即 `∀ n → f n ≡ g n`
--
-- 解决的问题：
--   List 表示下 `sums (c₁ , n₁) ((c₁ , n₁) ∷ xs)` 因 `n₁ ≟ n₁` Stuck。
--   函数表示下 `sums (c₁ , n₁) f = f n₁` —— 直接应用，无比较。

module Sovereign.Algebra.LaurentFn where

open import Data.Integer.Base using (ℤ; +_; -[1+_]; _+_; _*_; -_; _-_)
open import Data.Integer.Properties using (+-assoc; +-comm; +-identityʳ; +-identityˡ;
  *-assoc; *-comm; *-identityʳ; *-identityˡ; distribʳ; distribˡ; *-zeroʳ; *-zeroˡ;
  *-distribʳ-+; *-distribˡ-+)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.List.Base using (List; []; _∷_; _++_; map; foldr)
open import Data.Empty using (⊥; ⊥-elim)

-- ────────────────────────────────────────────────────────────────────
-- 函数表示的 Laurent 多项式
-- ────────────────────────────────────────────────────────────────────

-- Laurent 多项式 = 有限支撑函数 ℤ → ℤ
-- （有限支撑由使用侧保证：只在有限多个指数上非零）
Laurent : Set
Laurent = ℤ → ℤ

-- 测试项（指数）
Exponent : Set
Exponent = ℤ

-- 逐指数系数和：直接应用，无 _≟_！
sums : Exponent → Laurent → ℤ
sums n f = f n

-- ────────────────────────────────────────────────────────────────────
-- 逐点相等（外延相等的替代）
-- ────────────────────────────────────────────────────────────────────

-- 逐点相等：∀ n → f n ≡ g n
-- 这是函数外延性的"点态"版本，无需 funext 公理
_≈_ : Laurent → Laurent → Set
f ≈ g = ∀ n → f n ≡ g n

-- 逐点相等是等价关系
≈-refl : ∀ f → f ≈ f
≈-refl f = λ n → refl

≈-sym : ∀ {f g} → f ≈ g → g ≈ f
≈-sym p = λ n → sym (p n)

≈-trans : ∀ {f g h} → f ≈ g → g ≈ h → f ≈ h
≈-trans p q = λ n → trans (p n) (q n)

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique（函数表示下平凡！）
-- ────────────────────────────────────────────────────────────────────

-- 核心定理：若对所有测试项 sums 相等，则逐点相等
-- 在函数表示下，这直接就是假设本身！
canon-sums-unique : ∀ (f g : Laurent) →
  (∀ u → sums u f ≡ sums u g) → f ≈ g
canon-sums-unique f g h = h

-- ────────────────────────────────────────────────────────────────────
-- 零多项式与常数
-- ────────────────────────────────────────────────────────────────────

-- 零多项式
R0 : Laurent
R0 = λ _ → + 0

-- 单项式 c·t^n（用 case_of_ 避免 if 语法）
case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

mono : ℤ → Exponent → Laurent
mono c n = λ m → case (m ≟ n) of λ
  { (yes _) → c
  ; (no _) → + 0
  }
  where open import Data.Integer.Properties using (_≟_)
        open import Relation.Nullary using (Dec; yes; no)

-- t
tvar : Laurent
tvar = mono (+ 1) (+ 1)

-- t⁻¹
tinv : Laurent
tinv = mono (+ 1) -[1+ 0 ]

-- ────────────────────────────────────────────────────────────────────
-- 加法与乘法（卷积）
-- ────────────────────────────────────────────────────────────────────

-- 加法：逐点加法
_+L_ : Laurent → Laurent → Laurent
(f +L g) n = f n + g n

-- 乘法：卷积（需要有限支撑信息，待后续定义）
-- (f *L g) n = Σ_k f k * g (n - k)
-- _*L_ : Laurent → Laurent → Laurent

-- ────────────────────────────────────────────────────────────────────
-- 加法性质
-- ────────────────────────────────────────────────────────────────────

+L-assoc : ∀ f g h → ((f +L g) +L h) ≈ (f +L (g +L h))
+L-assoc f g h n = +-assoc (f n) (g n) (h n)

+L-comm : ∀ f g → (f +L g) ≈ (g +L f)
+L-comm f g n = +-comm (f n) (g n)

+L-identityʳ : ∀ f → (f +L R0) ≈ f
+L-identityʳ f n = +-identityʳ (f n)

+L-identityˡ : ∀ f → (R0 +L f) ≈ f
+L-identityˡ f n = +-identityˡ (f n)
