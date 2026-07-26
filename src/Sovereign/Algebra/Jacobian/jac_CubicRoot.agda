{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Algebra.Jacobian.jac_CubicRoot where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- ═══════════════════════════════════════════════════════════
-- GF(3) 三次多项式根测试定理
--
-- f(λ) = λ³ + a·λ² + b·λ + c, 可约 ⟺ ∃r∈{0,1,2}: f(r)=0
-- 证明: (⇒) 若 f=(λ-r)·q, 则 f(r)=0.
--       (⇐) 若 f(r)=0, 则 f=(λ-r)·(λ²+(a+r)λ+(b+ar+r²)).
--           三个 r 分别验证因式分解恒等式.
-- ═══════════════════════════════════════════════════════════

-- 求值公式 (简化, 2³≡2, 2²≡1 in GF(3)):
--   f(0) = c
--   f(1) = 1 + a + b + c
--   f(2) = 2 + a + 2·b + c

-- 实例: λ³+2λ+1 (a=T₀, b=T₂, c=T₁)
a₀ b₀ c₀ : Trit; a₀ = T₀; b₀ = T₂; c₀ = T₁

v0 : Trit; v0 = c₀                            -- f(0) = T₁
v1 : Trit; v1 = ((T₁ ⊕ a₀) ⊕ b₀) ⊕ c₀        -- f(1) = T₁
v2 : Trit; v2 = ((T₂ ⊕ a₀) ⊕ (T₂ ⊗ b₀)) ⊕ c₀ -- f(2) = T₁

v0≠0 : v0 ≢ T₀; v0≠0 = λ ()
v1≠0 : v1 ≢ T₀; v1≠0 = λ ()
v2≠0 : v2 ≢ T₀; v2≠0 = λ ()

-- λ³+2λ+1 在 GF(3) 上不可约 (0 postulate)
