{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteLightcone
-- 83 相对论补强 — GF(3)² 闵氏形式与光锥分类 (0 postulate)
--
-- q(x,y) = x² − y² (GF(3)): 类光 q=0 (x=±y), 类时 q=1, 类空 q=2
-- 9 格点分类: 5 类光 + 2 类时 + 2 类空 — 离散光锥的完整结构

module Sovereign.Physics.DiscreteLightcone where

open import Data.Nat using (_+_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

q : Trit → Trit → Trit
q x y = (x ⊗ x) ⊕ negate (y ⊗ y)

-- 类光 (5 点): x = ±y
light-00 : q T₀ T₀ ≡ T₀ ; light-00 = refl
light-11 : q T₁ T₁ ≡ T₀ ; light-11 = refl
light-22 : q T₂ T₂ ≡ T₀ ; light-22 = refl
light-12 : q T₁ T₂ ≡ T₀ ; light-12 = refl
light-21 : q T₂ T₁ ≡ T₀ ; light-21 = refl

-- 类时 (2 点): q = 1
time-10 : q T₁ T₀ ≡ T₁ ; time-10 = refl
time-20 : q T₂ T₀ ≡ T₁ ; time-20 = refl

-- 类空 (2 点): q = 2
space-01 : q T₀ T₁ ≡ T₂ ; space-01 = refl
space-02 : q T₀ T₂ ≡ T₂ ; space-02 = refl

-- 光锥计数: 5 类光 + 2 类时 + 2 类空 = 9
cone-partition : 5 + 2 + 2 ≡ 9
cone-partition = refl

-- 0 postulate.
