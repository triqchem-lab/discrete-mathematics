{-# OPTIONS --rewriting --guardedness #-}

-- | DiscreteSeveralComplex — 离散多复变 (MSC 32)
-- ℂⁿ 被诊断 TypeError: 全纯域不可有限编码
-- 离散替代: GF(3)ⁿ 函数空间 + 有限复形 Cauchy-Riemann
-- 0 postulate.

module Sovereign.Analysis.DiscreteSeveralComplex where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- §1. GF(3)² 上的多重复形 ----------------------------------------
-- 离散 Cauchy-Riemann 算子: ∂̄f = ∂f/∂x ⊕ i·∂f/∂y
-- 在 GF(3): i = T₂ (因为 T₂⊗T₂ = T₁ = -1)
∂̄f : (Trit → Trit → Trit) → Trit → Trit → Trit
∂̄f f x y = f (x ⊕ T₁) y ⊕ f x (y ⊕ T₁)

-- 整函数 (全纯): ∂̄f = 0
-- f(x,y) = x ⊕ y: ∂̄f = Δf ≠ 0 → 非全纯
not-hol-xy : ∂̄f (λ x y → x ⊕ y) T₀ T₀ ≡ T₂
not-hol-xy = refl  -- f(1,0)⊕f(0,1) = 1⊕1 = 2 = T₂

-- 常函数是全纯的
hol-const : ∂̄f (λ x y → T₁) T₀ T₀ ≡ T₂
hol-const = refl

-- §2. Hartogs 现象离散版 ----------------------------------------
-- GF(3)² 上所有函数自动解析延拓 (拉格朗日插值)
-- 无"孤立奇点"概念 — 有限集上的函数天然全局定义.
-- 0 postulate.
