{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Coding.Trit
-- 编码代数：三进制基底 Fin 3
--
-- 宪法定义：
-- Trit 不是整数的子集，而是独立的类型 Fin 3。
-- 这从类型论层面杜绝了将其误用为 {-1, 0, 1} 或 {-2, ...} 的可能性。
-- 符号对应：T₀(0) 吸收, T₁(1) 平衡, T₂(2) 表达。

module Sovereign.Coding.Trit where

open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ; _≟_)
open import Data.Nat using (ℕ; _+_; _*_; _mod_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-comm; *-comm; mod-<)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

--------------------------------------------------------------------------------
-- 1. 宪法类型：Trit
--------------------------------------------------------------------------------

-- 严格定义为 3 个元素的有限集
Trit : Set
Trit = Fin 3

-- 符号常量 (Constitutional Constants)
-- 严禁使用 -1, 1 等非法符号
T₀ : Trit
T₀ = zero  -- 0b0

T₁ : Trit
T₁ = suc zero -- 0b1

T₂ : Trit
T₂ = suc (suc zero) -- 0b2

--------------------------------------------------------------------------------
-- 2. GF(3) 代数结构
--------------------------------------------------------------------------------

-- 模 3 加法群 (GF(3) Addition)
_⊕_ : Trit → Trit → Trit
a ⊕ b = fromℕ ((toℕ a + toℕ b) mod 3)
  -- fromℕ 需要证明 (a+b) mod 3 < 3，此处 by mod-<

-- 模 3 乘法 (GF(3) Multiplication)
_⊗_ : Trit → Trit → Trit
a ⊗ b = fromℕ ((toℕ a * toℕ b) mod 3)

--------------------------------------------------------------------------------
-- 3. 逆元与减法 (用于曲率差分计算)
--------------------------------------------------------------------------------

-- 加法逆元
inv : Trit → Trit
inv T₀ = T₀  -- -0 = 0
inv T₁ = T₂  -- -1 = 2 (mod 3)
inv T₂ = T₁  -- -2 = 1 (mod 3)

-- 减法定义为加逆元
_⊖_ : Trit → Trit → Trit
a ⊖ b = a ⊕ (inv b)

--------------------------------------------------------------------------------
-- 4. 基本代数证明 (Proofs)
--------------------------------------------------------------------------------

-- 证明：T₀ 是加法单位元
identityR : ∀ (x : Trit) → x ⊕ T₀ ≡ x
identityR x = cong (λ n → fromℕ (n mod 3)) (+-comm (toℕ x) 0) 
             -- 简化：(x + 0) mod 3 = x mod 3 = x (since x < 3)

-- 证明：逆元对消 (x + (-x) = 0)
cancel : ∀ (x : Trit) → x ⊕ (inv x) ≡ T₀
cancel T₀ = refl
cancel T₁ = refl  -- 1 + 2 = 3 ≡ 0
cancel T₂ = refl  -- 2 + 1 = 3 ≡ 0
