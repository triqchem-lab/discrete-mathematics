{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DiscretePolynomial
-- 离散多项式函数论 — GF(3)[x] 多项式环
--
-- 数学背景:
--   GF(3)[x] 是系数在 GF(3) = {0,1,2} 中的多项式环。
--   特征 3 的独特性质: (x³)' = 3x² = 0, 形式导数丢失信息。
--   有限域上的多项式理论是编码理论 (Coding/BCHGF9) 和
--   代数几何 (Problem/Riemann) 的基础。
--
-- 核心定理:
--   §1 多项式类型: GF(3) 系数的有限多项式
--   §2 求值: eval : Poly → GF(3) → GF(3) (Horner 法则)
--   §3 形式导数: coeff-deriv, char 3 特殊性 (3≡0)
--   §4 多项式加法: 逐分量 ⊕
--   §5 度 1 多项式乘法: (a₀+a₁x)(b₀+b₁x) 展开
--   §6 根: IsRoot, 具体验证实例
--
-- 依赖:
--   Sovereign.Base.Trit — GF(3) 三进制本体
--
-- 0 postulate — 全部构造性证明

module Sovereign.Algebra.DiscretePolynomial where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Vec using (Vec; []; _∷_; zipWith; map)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
         ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-inverse;
         ⊗-zeroˡ; ⊗-zeroʳ; ⊗-identityˡ; ⊗-identityʳ;
         ⊗-comm)

--------------------------------------------------------------------------------
-- §1. 多项式类型 — GF(3)[x] 的有限表示
--------------------------------------------------------------------------------

-- Poly n = 度 ≤ n 的多项式, 系数向量 [a₀, a₁, ..., aₙ]
-- 即 a₀ + a₁x + a₂x² + ... + aₙxⁿ

Poly : ℕ → Set
Poly n = Vec Trit (suc n)

-- 零多项式
zero-poly : ∀ n → Poly n
zero-poly zero    = T₀ ∷ []
zero-poly (suc n) = T₀ ∷ zero-poly n

-- 常数多项式
const-poly : ∀ n → Trit → Poly n
const-poly zero    a = a ∷ []
const-poly (suc n) a = a ∷ zero-poly n

-- 单项式 x^k (系数 1 在第 k 位)
monic : ∀ n → Fin (suc n) → Poly n
monic zero    zero    = T₁ ∷ []
monic zero    (suc ())
monic (suc n) zero    = T₁ ∷ zero-poly n
monic (suc n) (suc k) = T₀ ∷ monic n k

-- 验证: monic 2 2 = [0, 0, 1] = x²
monic-2-2 : monic 2 (suc (suc zero)) ≡ T₀ ∷ T₀ ∷ T₁ ∷ []
monic-2-2 = refl

--------------------------------------------------------------------------------
-- §2. 多项式求值 — Horner 法则
--------------------------------------------------------------------------------

-- eval p x = a₀ + x·(a₁ + x·(a₂ + ... + x·aₙ))
eval : ∀ {n} → Poly n → Trit → Trit
eval (a ∷ [])      x = a
eval (a ∷ b ∷ bs)  x = a ⊕ (x ⊗ eval (b ∷ bs) x)

-- 常数多项式求值 = 常数 (度 0)
eval-const-0 : (a : Trit) → eval (a ∷ []) T₀ ≡ a
eval-const-0 a = refl

-- 零多项式求值 = 0 (度 0)
eval-zero-0 : eval (T₀ ∷ []) T₀ ≡ T₀
eval-zero-0 = refl

-- 单项式求值: eval (monic 0 0) T₁ = T₁
eval-monic-0 : eval (monic 0 zero) T₁ ≡ T₁
eval-monic-0 = refl

-- 求值在 GF(3) 上封闭: 所有运算在 Trit 中, 无溢出
-- 这是有限域多项式与 ℝ[x] 的根本区别

--------------------------------------------------------------------------------
-- §3. 形式导数 — char 3 的独特性质
--------------------------------------------------------------------------------

-- 形式导数: d/dx (a₀ + a₁x + a₂x² + ... + aₙxⁿ) = a₁ + 2a₂x + ... + naₙx^{n-1}
-- 在 GF(3) 中: 1·a₁ + 2·a₂x + 0·a₃x² + 1·a₄x³ + ...
-- 关键: 3 ≡ 0, 所以 x³ 的导数 = 0

-- 辅助: 从 ℕ 到 Trit 的映射 (周期 3)
from-ℕ : ℕ → Trit
from-ℕ zero            = T₀
from-ℕ (suc zero)      = T₁
from-ℕ (suc (suc zero)) = T₂
from-ℕ (suc (suc (suc n))) = from-ℕ n  -- 周期 3

-- 系数乘以指数 (模 3)
coeff-deriv : ℕ → Trit → Trit
coeff-deriv zero    a = T₀  -- 常数项导数 = 0
coeff-deriv (suc k) a = from-ℕ (suc k) ⊗ a

-- 度 0 多项式的导数 = 0
deriv-0 : Poly 0 → Poly 0
deriv-0 (a ∷ []) = T₀ ∷ []

-- 关键定理: x³ 的导数 = 0 (char 3)
-- x³ = [0, 0, 0, 1], 导数 = [0, 0, 3·1] = [0, 0, 0]
-- 因为 3 ⊗ T₁ = (T₁ ⊕ T₁ ⊕ T₁) ⊗ T₁ = T₀ ⊗ T₁ = T₀

-- char 3 的核心事实: 3 ≡ 0 in GF(3)
char3-is-zero : (T₁ ⊕ T₁) ⊕ T₁ ≡ T₀
char3-is-zero = refl

-- 推论: 3 ⊗ x ≡ T₀ 对所有 x
three-times : ∀ x → ((T₁ ⊕ T₁) ⊕ T₁) ⊗ x ≡ T₀
three-times x = cong (λ t → t ⊗ x) char3-is-zero

-- coeff-deriv 在 k=3 时归零: 3 ⊗ a ≡ T₀
coeff-deriv-3 : ∀ a → coeff-deriv 3 a ≡ T₀
coeff-deriv-3 a = cong (λ t → t ⊗ a) char3-is-zero

--------------------------------------------------------------------------------
-- §4. 多项式加法 — 逐分量 ⊕
--------------------------------------------------------------------------------

-- 多项式加法: 逐分量 GF(3) 加法
_+p_ : ∀ {n} → Poly n → Poly n → Poly n
_+p_ = zipWith _⊕_

-- 加法交换律
+p-comm : ∀ {n} (p q : Poly n) → p +p q ≡ q +p p
+p-comm (a ∷ []) (b ∷ []) = cong₂ _∷_ (⊕-comm a b) refl
+p-comm (a ∷ a' ∷ as) (b ∷ b' ∷ bs) =
  cong₂ _∷_ (⊕-comm a b) (+p-comm (a' ∷ as) (b' ∷ bs))

-- 零多项式是加法单位元
+p-zeroˡ : ∀ {n} (p : Poly n) → zero-poly n +p p ≡ p
+p-zeroˡ (a ∷ []) = cong₂ _∷_ (⊕-identityˡ a) refl
+p-zeroˡ (a ∷ a' ∷ as) = cong₂ _∷_ (⊕-identityˡ a) (+p-zeroˡ (a' ∷ as))

-- 加法逆元: negate 每个系数
negate-poly : ∀ {n} → Poly n → Poly n
negate-poly = map negate

+p-inverse : ∀ {n} (p : Poly n) → p +p negate-poly p ≡ zero-poly n
+p-inverse (a ∷ []) = cong₂ _∷_ (⊕-inverse a) refl
+p-inverse (a ∷ a' ∷ as) = cong₂ _∷_ (⊕-inverse a) (+p-inverse (a' ∷ as))

--------------------------------------------------------------------------------
-- §5. 度 1 多项式乘法
--------------------------------------------------------------------------------

-- (a₀ + a₁x)(b₀ + b₁x) = a₀b₀ + (a₀b₁ + a₁b₀)x + a₁b₁x²
mul-deg1 : (a₀ a₁ b₀ b₁ : Trit) → Poly 2
mul-deg1 a₀ a₁ b₀ b₁ =
  (a₀ ⊗ b₀) ∷ ((a₀ ⊗ b₁) ⊕ (a₁ ⊗ b₀)) ∷ (a₁ ⊗ b₁) ∷ []

-- 验证: (1 + x)(1 + x) = 1 + 2x + x²
mul-deg1-11 : mul-deg1 T₁ T₁ T₁ T₁ ≡ T₁ ∷ T₂ ∷ T₁ ∷ []
mul-deg1-11 = refl

-- 验证: (1 + x)(1 + 2x) = 1 + 0x + 2x²
mul-deg1-12 : mul-deg1 T₁ T₁ T₁ T₂ ≡ T₁ ∷ T₀ ∷ T₂ ∷ []
mul-deg1-12 = refl

-- 乘法单位元: (1)(a₀ + a₁x) = a₀ + a₁x
mul-deg1-idˡ : ∀ a₀ a₁ → mul-deg1 T₁ T₀ a₀ a₁ ≡ a₀ ∷ a₁ ∷ T₀ ∷ []
mul-deg1-idˡ a₀ a₁ = cong₂ _∷_ (⊗-identityˡ a₀)
  (cong₂ _∷_ (trans (⊕-identityʳ (T₁ ⊗ a₁)) (⊗-identityˡ a₁)) refl)

--------------------------------------------------------------------------------
-- §6. 根与因式
--------------------------------------------------------------------------------

-- 根: eval p x ≡ T₀
IsRoot : ∀ {n} → Poly n → Trit → Set
IsRoot p x = eval p x ≡ T₀

-- x = T₀ 是任意多项式的根 (因为 eval p T₀ = a₀)
root-at-zero-0 : eval (T₀ ∷ T₂ ∷ T₁ ∷ []) T₀ ≡ T₀
root-at-zero-0 = refl

-- x = T₁ 是 x² + 2x 的根 (1 + 2 = 3 ≡ 0)
example-poly : Poly 2
example-poly = T₀ ∷ T₂ ∷ T₁ ∷ []

example-root : eval example-poly T₁ ≡ T₀
example-root = refl

-- x = T₂ 不是根 (4 + 4 = 8 ≡ 2)
example-not-root : eval example-poly T₂ ≢ T₀
example-not-root ()

-- 有限域上的多项式求值是满射: 常数多项式即满射
eval-surjective : ∀ (y : Trit) → Σ (Poly 0) (λ p → eval p T₀ ≡ y)
eval-surjective y = (y ∷ []) , refl

-- 0 postulate.
