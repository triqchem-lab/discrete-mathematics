{-# OPTIONS --rewriting --guardedness #-}

-- | DiscretePotential — 离散位势论 (MSC 31)
-- GF(3) 格点上的 Laplace 方程 Δu = f.
-- 0 postulate.

-- | 离散位势论实例核
--
-- 核心原则：离散位势论实例核——离散基座实例核（非一般定理，诚实边界随引用）
--          穷举/归纳边界遵守（≤27 case 或具名链，trans ≤3）
--          代数污染禁令（禁 Float/Double/超越函数）
--
-- 包含：laplace3、laplace-const、laplace-linear、laplace-quadratic、harmonic-const、laplace3-cyclic

module Sovereign.Application.DiscretePotential where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; ⊕-assoc; ⊕-comm)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; module ≡-Reasoning)

-- §1. 三点离散 Laplacian ------------------------------------------
-- Δu(i) = u(i-1) + u(i+1) - 2u(i) → 在 GF(3): -2u = T₁·u.
laplace3 : Trit → Trit → Trit → Trit
laplace3 u0 u1 u2 = (u0 ⊕ u2) ⊕ u1  -- u₀+u₂+u₁

-- 常函数在 GF(3) 的 Laplacian = 0
laplace-const : laplace3 T₁ T₁ T₁ ≡ T₀
laplace-const = refl  -- 1+1+1=3≡0 ✓

-- 线性函数 u = [T₀, T₁, T₂] 的 Laplacian
laplace-linear : laplace3 T₀ T₁ T₂ ≡ T₀
laplace-linear = refl  -- 0+2+1=3≡0 ✓

-- 二次函数 u = [T₀, T₁, T₁] 的 Laplacian
laplace-quadratic : laplace3 T₀ T₁ T₁ ≡ T₂
laplace-quadratic = refl  -- 0+1+1=2≡T₂ ✓

-- 调和函数: Δu=0 的解为常数和线性
harmonic-const : laplace3 T₀ T₀ T₀ ≡ T₀
harmonic-const = refl

-- 经典位势依赖 ℂ 的 Poisson 核和 Green 函数.
-- 离散替代: GF(3) 上有限差分算子穷举求解.
-- 0 postulate.

-- 一般 ∀ 定理：laplace3 的循环不变性（⊕ AC 性——5 步代数链）
laplace3-cyclic : ∀ a b c → laplace3 a b c ≡ laplace3 b c a
laplace3-cyclic a b c = begin
  (a ⊕ c) ⊕ b
    ≡⟨ ⊕-assoc a c b ⟩
  a ⊕ (c ⊕ b)
    ≡⟨ cong (a ⊕_) (⊕-comm c b) ⟩
  a ⊕ (b ⊕ c)
    ≡⟨ sym (⊕-assoc a b c) ⟩
  (a ⊕ b) ⊕ c
    ≡⟨ cong (_⊕ c) (⊕-comm a b) ⟩
  (b ⊕ a) ⊕ c
  ∎
  where open ≡-Reasoning
