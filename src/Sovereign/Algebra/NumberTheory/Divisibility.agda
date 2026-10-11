{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.NumberTheory.Divisibility
-- 数学背景：整除 ∣、最大公因数 gcd、最小公倍数 lcm、Bézout 恒等式——
--   数论第一基石。对标整合层：stdlib `Data.Nat.Divisibility`/`Data.Nat.GCD`
--   （含 Bézout 引理证明——存在性对标引用不重证）为信任基座；本库补：
--   ① ∣-∸（整除对减法封闭——辗转相减的代数根据，Euclid 算法根基）；
--   ② IsGCD 关系形（关系入定义口径——极大性为字段非公理）；
--   ③ BezoutIdentity 关系形 + 具体实例核对层（12/8/4 族）。
-- 核心原则：
-- 1. 复用优先：stdlib 定理不重证（gcd/lcm 计算面直接引用）
-- 2. 0 postulate / 0 hole
-- 3. 关系入定义（IsGCD/BezoutIdentity 为 record/Σ 形）
-- 4. 通用引理层（§1-§2）与数值核对层（§4）分层
-- 包含：∸-+-cancelʳ · ∣-∸ · IsGCD · BezoutIdentity · 实例核对 ×4

module Sovereign.Algebra.NumberTheory.Divisibility where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.GCD using (gcd)
open import Data.Nat.LCM using (lcm)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Data.Nat.Properties using (+-identityʳ; +-comm)

--------------------------------------------------------------------------------
-- §1 基础件层：减法消去与分配（辗转相减的代数根据）
--------------------------------------------------------------------------------

-- +-suc′：a + suc c ≡ suc (a + c)（尾后继前移）
+-suc′ : ∀ a c → a + suc c ≡ suc (a + c)
+-suc′ zero    c = refl
+-suc′ (suc a) c = cong suc (+-suc′ a c)

-- zero-∸：0 ∸ x ≡ 0（_∸_ 首子句匹配二参——归纳助件）
zero-∸ : ∀ x → zero ∸ x ≡ zero
zero-∸ zero   = refl
zero-∸ (suc x) = refl

-- ∸-+-cancelʳ：同加尾项对减法消去 —— (a + c) ∸ (b + c) ≡ a ∸ b
∸-+-cancelʳ : ∀ a b c → (a + c) ∸ (b + c) ≡ a ∸ b
∸-+-cancelʳ a b zero    = cong₂ _∸_ (+-identityʳ a) (+-identityʳ b)
∸-+-cancelʳ a b (suc c) =
  trans (cong ((a + suc c) ∸_) (+-suc′ b c))
        (trans (cong (λ z → z ∸ suc (b + c)) (+-suc′ a c))
               (∸-+-cancelʳ a b c))

-- *-∸-factor：分配抽取 —— (q₁*d) ∸ (q₂*d) ≡ (q₁ ∸ q₂)*d
*-∸-factor : ∀ q₁ q₂ d → (q₁ * d) ∸ (q₂ * d) ≡ (q₁ ∸ q₂) * d
*-∸-factor zero    q₂       d =
  trans (zero-∸ (q₂ * d)) (sym (cong (λ z → z * d) (zero-∸ q₂)))
*-∸-factor (suc p) zero     d = refl
*-∸-factor (suc p) (suc q)  d =
  trans (cong (λ z → z ∸ (d + q * d)) (+-comm d (p * d)))
        (trans (cong (λ z → (p * d + d) ∸ z) (+-comm d (q * d)))
               (trans (∸-+-cancelʳ (p * d) (q * d) d) (*-∸-factor p q d)))

--------------------------------------------------------------------------------
-- §2 主引理层：∣-∸（整除对减法封闭）
--------------------------------------------------------------------------------

-- ∣-∸：d ∣ a → d ∣ b → b ≤ a → d ∣ (a ∸ b)
-- 数学理由：a = q₁d、b = q₂d ⟹ a - b = (q₁ ∸ q₂)d（b ≤ a 无借位）
∣-∸ : ∀ {a b d} → d ∣ a → d ∣ b → b ≤ a → d ∣ (a ∸ b)
∣-∸ {d = d} (divides q₁ refl) (divides q₂ refl) _ =
  divides (q₁ ∸ q₂) (*-∸-factor q₁ q₂ d)

--------------------------------------------------------------------------------
-- §3 组合层：IsGCD 关系形 + Bézout 关系形（关系入定义）
--------------------------------------------------------------------------------

-- IsGCD a b g：g 是 a、b 的最大公因数（因子性 + 极大性为字段）
record IsGCD (a b g : ℕ) : Set where
  field
    ∣-left   : g ∣ a
    ∣-right  : g ∣ b
    greatest : ∀ d → d ∣ a → d ∣ b → d ∣ g

-- BezoutIdentity a b g：s*a = g + t*b（ℕ 无符号 Bézout 形）
BezoutIdentity : ℕ → ℕ → ℕ → Set
BezoutIdentity a b g = Σ ℕ λ s → Σ ℕ λ t → s * a ≡ g + t * b

-- 对标注记：gcd 存在性/唯一性与 Bézout 存在性由 stdlib `Data.Nat.GCD`
-- （gcd 函数 + GCD record + Bézout 模块）承载——本模块不重证。

--------------------------------------------------------------------------------
-- §4 核对层：具体实例（数值通道）
--------------------------------------------------------------------------------

8≤12 : 8 ≤ 12
8≤12 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

12∸8≡4 : 12 ∸ 8 ≡ 4
12∸8≡4 = refl

-- IsGCD 12 8 4：因子性（4∣12 商 3、4∣8 商 2）+ 极大性（经 ∣-∸ 通道自洽）
isGcd-12-8-4 : IsGCD 12 8 4
isGcd-12-8-4 = record
  { ∣-left   = divides 3 refl
  ; ∣-right  = divides 2 refl
  ; greatest = greatest-12-8
  }
  where
  greatest-12-8 : ∀ d → d ∣ 12 → d ∣ 8 → d ∣ 4
  greatest-12-8 d h₁ h₂ = lemma d (∣-∸ h₁ h₂ 8≤12)
    where
    lemma : ∀ d → d ∣ (12 ∸ 8) → d ∣ 4
    lemma d (divides q eq) = divides q (trans (sym 12∸8≡4) eq)

-- Bezout 12 8 4：s = 1、t = 1 —— 1·12 = 4 + 1·8
bezout-12-8-4 : BezoutIdentity 12 8 4
bezout-12-8-4 = 1 , 1 , refl

-- gcd/lcm 计算面对账（stdlib 计算性核对）
check-gcd-12-8 : gcd 12 8 ≡ 4
check-gcd-12-8 = refl

check-lcm-3-4 : lcm 3 4 ≡ 12
check-lcm-3-4 = refl
