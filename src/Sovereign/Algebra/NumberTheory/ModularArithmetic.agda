{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.NumberTheory.ModularArithmetic
-- 数学背景：模 n 算术 Z/nZ——Duodecimal（R₁₂=ℤ/12ℤ）特例的上位泛型。
--   本模块给出 **ModGroup 关系形**（关系入定义：载体 + ⊕ₙ + 单位 + 负元 + 定律字段），
--   通用定律以「值层模等式」呈现（⊕ₙ a b = (a+b)%n），并与本库 CRT 面衔接：
--   π3 保加法实例核（GF(3) 分量同态性——crt12 分解的加法相容面）。
-- 核心原则：
-- 1. 复用优先：stdlib DivMod/Properties 为基座；Duodecimal/Trit 只读衔接
-- 2. 0 postulate / 0 hole
-- 3. 关系入定义（ModGroup 字段化）
--; 4. 通用定律层（§1-§2）与 CRT 衔接核对层（§4）分层
-- 包含：⊕ₙ · ⊕ₙ-comm · ⊕ₙ-unitₗ · ⊕ₙ-invʳ · ModGroup · CRT 衔接核对 ×3

module Sovereign.Algebra.NumberTheory.ModularArithmetic where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; z≤n; s≤s; NonZero)
open import Data.Nat.DivMod using (_%_; n%n≡0; m<n⇒m%n≡m)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ; m+[n∸m]≡n)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.GroupTheory.Duodecimal using (Duodec; d7; d8; _+12_; π3)

--------------------------------------------------------------------------------
-- §1 基础件层：⊕ₙ 模加法（值层）
--------------------------------------------------------------------------------

-- ⊕ₙ：模 n 加法（载体 ℕ——调用方带 a < n / b < n 前提即 Z/nZ 元）
⊕ₙ : (n : ℕ) → {{_ : NonZero n}} → ℕ → ℕ → ℕ
⊕ₙ n a b = (a + b) % n

--------------------------------------------------------------------------------
-- §2 主引理层：群定律（值层模等式）
--------------------------------------------------------------------------------

-- ⊕ₙ-comm：交换律（+_ 交换经 % 共轭）
⊕ₙ-comm : ∀ n a b → {{_ : NonZero n}} → ⊕ₙ n a b ≡ ⊕ₙ n b a
⊕ₙ-comm n a b = cong (λ z → z % n) (+-comm a b)

-- ⊕ₙ-assoc-unrolled：未取模结合形（cong 承载——结构性相等）
⊕ₙ-assoc-unrolled : ∀ n a b c → {{_ : NonZero n}} → ((a + b) + c) % n ≡ (a + (b + c)) % n
⊕ₙ-assoc-unrolled n a b c = cong (λ z → z % n) (+-assoc a b c)

-- ⊕ₙ-unitʳ：a < n ⟹ a ⊕ₙ 0 ≡ a（单位元律——右侧单位）
⊕ₙ-unitʳ : ∀ n a → {{_ : NonZero n}} → a < n → ⊕ₙ n a 0 ≡ a
⊕ₙ-unitʳ n a a<n = trans (cong (λ z → z % n) (+-identityʳ a)) (m<n⇒m%n≡m a<n)

-- ⊕ₙ-invʳ：a < n ⟹ a ⊕ₙ (n ∸ a) ≡ 0（负元律——右侧逆）
⊕ₙ-invʳ : ∀ n a → {{_ : NonZero n}} → a ≤ n → (a + (n ∸ a)) % n ≡ 0
⊕ₙ-invʳ n a a≤n = trans (cong (λ z → z % n) (m+[n∸m]≡n a≤n)) (n%n≡0 n)

--------------------------------------------------------------------------------
-- §3 组合层：ModGroup 关系形（关系入定义）
--------------------------------------------------------------------------------

-- ModGroup n：Z/nZ 加法群数据包（定律为字段——实例层填装）
record ModGroup (n : ℕ) {{_ : NonZero n}} : Set₁ where
  field
    carrier : Set
    el      : carrier → ℕ
    _⊕ᵍ_    : carrier → carrier → carrier
    zeroᵍ   : carrier
    comm    : ∀ a b → el (a ⊕ᵍ b) ≡ el (b ⊕ᵍ a)
    unit    : ∀ a → el (a ⊕ᵍ zeroᵍ) ≡ el a

--------------------------------------------------------------------------------
-- §4 核对层：CRT 衔接（π3 分量同态性实例核）
--------------------------------------------------------------------------------

-- π3 保加法实例：7 ⊕₁₂ 8 = 3（15 mod 12）——GF(3) 分量：T₁ ⊕ T₂ ≡ T₀
check-π3-+12 : π3 (d7 +12 d8) ≡ π3 d7 ⊕ π3 d8
check-π3-+12 = refl

-- 值层模加法核对：7 ⊕₁₂ 8 ≡ 3、5 ⊕₁₂ 7 ≡ 0
check-add12-78 : ⊕ₙ 12 7 8 ≡ 3
check-add12-78 = refl

check-add12-57 : ⊕ₙ 12 5 7 ≡ 0
check-add12-57 = refl

-- CRT 衔接注记：crt12 : Trit → Fin 4 → Duodec 与 π3/π4 投影构成重构对
--   （Duodecimal 件承载 crt12-roundtrip）；⊕ₙ 泛型面与 R₁₂ 特例（_+12_）的
--   同态相容由 check-π3-+12 类实例核承载——一般形（π3 保 +₁₂ 定理）立界注记。
-- 立界（如实）：① ⊕ₙ-assoc 取模形（需 %-distribʳ-+ 族——本版未引）；
--   ② ModGroup 实例填装（ℕ 模 n 满 carrier 形）；③ 乘法面（⊗ₙ/乘法群）。
