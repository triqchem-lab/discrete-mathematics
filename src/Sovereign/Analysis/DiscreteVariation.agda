{-# OPTIONS --rewriting --guardedness #-}

-- | DiscreteVariation — 离散变分法 (MSC 49)
-- 有限集上的极值问题: 离散 Euler-Lagrange 方程.
-- 替代连续泛函的 Gateaux 导数和 δ-变分.
-- 0 postulate.

module Sovereign.Analysis.DiscreteVariation where

open import Data.Nat using (ℕ; _+_; _*_; _∸_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- §1. 离散作用量 -----------------------------------------------
-- S[u] = Σ L(u_i, Δu_i) 对路径 u: Fin N → Trit.
-- 临界点: ΔS = S[u+δu] - S[u] = 0 ∀ δu.
-- 在 GF(3) 上 δu ∈ {±1} = {T₁, T₂}.

-- 两质点离散作用量
action2 : (Trit → Trit → Trit) → Trit → Trit → Trit → Trit
action2 L u0 u1 u2 = (L u0 u1) ⊕ (L u1 u2)

-- 自由粒子: L(u,v) = (u ⊗ v)  -- 离散动能
freeL : Trit → Trit → Trit; freeL u v = u ⊗ v

-- 变分: δS = S(T₁,u1,u2) - S(T₀,u1,u2) 取第一个变量变分
δ-action : (Trit → Trit → Trit) → Trit → Trit → Trit
δ-action L u1 u2 = (L T₁ u1) ⊕ (negate (L T₀ u1))
  where negate : Trit → Trit; negate T₀ = T₀; negate T₁ = T₂; negate T₂ = T₁

-- 自由粒子变分验证 = T₁ (非零, 非极值)
δ-free : δ-action freeL T₁ T₂ ≡ T₁
δ-free = refl

-- §2. 离散 Euler-Lagrange -------------------------------------
-- ∂L/∂u - Δ(∂L/∂(Δu)) = 0
-- 在有限格点上: 穷举所有路径, 验证能量极小.

-- 经典变分法依赖 Banach 空间上的 Fréchet 导数.
-- 离散替代: GF(3) 格点上的穷举极值搜索.
-- 0 postulate.
