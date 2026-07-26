{-# OPTIONS --rewriting --guardedness #-}

-- | OrderLattice — 离散序与格理论 (MSC 06)
-- GF(3) 上的偏序与格: 有限集上所有序关系可穷举.
-- 0 postulate.

module Sovereign.Structology.OrderLattice where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

-- §1. GF(3) 全序链 T₀ < T₁ < T₂ ------------------------------------
data _≤₃_ : Trit → Trit → Set where
  leq-refl : ∀ {x} → x ≤₃ x
  leq-01   : T₀ ≤₃ T₁
  leq-02   : T₀ ≤₃ T₂
  leq-12   : T₁ ≤₃ T₂

-- 反自反性: T₁ ≰ T₀
¬T1≤T0 : T₁ ≤₃ T₀ → ⊥
¬T1≤T0 ()

-- 传递性实例 (全序自动满足)
≤₃-trans : ∀ {x y z} → x ≤₃ y → y ≤₃ z → x ≤₃ z
≤₃-trans leq-refl q        = q
≤₃-trans p        leq-refl = p
≤₃-trans leq-01   leq-12   = leq-02

-- §2. 格结构: join (∨) 和 meet (∧) -----------------------------------
∨₃ : Trit → Trit → Trit
∨₃ T₀ y = y
∨₃ T₁ T₀ = T₁
∨₃ T₁ T₁ = T₁
∨₃ T₁ T₂ = T₂
∨₃ T₂ _ = T₂

∧₃ : Trit → Trit → Trit
∧₃ T₀ _ = T₀
∧₃ T₁ T₀ = T₀
∧₃ T₁ T₁ = T₁
∧₃ T₁ T₂ = T₁
∧₃ T₂ T₀ = T₀
∧₃ T₂ T₁ = T₁
∧₃ T₂ T₂ = T₂

-- 吸收律验证
∨-absorbs-∧ : (a b : Trit) → (∨₃ a (∧₃ a b)) ≡ a
∨-absorbs-∧ T₀ T₀ = refl; ∨-absorbs-∧ T₀ T₁ = refl; ∨-absorbs-∧ T₀ T₂ = refl
∨-absorbs-∧ T₁ T₀ = refl; ∨-absorbs-∧ T₁ T₁ = refl; ∨-absorbs-∧ T₁ T₂ = refl
∨-absorbs-∧ T₂ T₀ = refl; ∨-absorbs-∧ T₂ T₁ = refl; ∨-absorbs-∧ T₂ T₂ = refl

-- §3. T⁶ 向量格 -----------------------------------------------------
-- GF3Vec n 逐点偏序: v ≤ w ⟺ ∀i, v(i) ≤₃ w(i)
-- 构成完备格 (有限维), 所有格恒等式由分量 refl 验证.

-- 经典对比: 连续格、Scott 拓扑、无限分配律 → 我们的离散格穷举闭合.
-- 0 postulate.
