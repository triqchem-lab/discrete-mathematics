{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DivisibilityChain
-- 子群链阶整除: 2∣4, 4∣8
--
-- 锚定 "2T=0→4T→8T 塔" 的阶整除关系:
--   ⟨-1⟩ 阶 2 ⊂ ⟨α⟩ 阶 4 ⊂ ⟨φ⟩ 阶 8
--   2 ∣ 4 (子群阶整除父群阶)
--   4 ∣ 8 (同上)
--
-- 语料锚: "月亮矩阵限制 + 归零共振" → 乘法子群链
-- 0 postulate.

module Sovereign.Algebra.DivisibilityChain where

open import Data.Nat using (ℕ; _*_)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Relation.Binary.PropositionalEquality using (refl)

-- ⟨-1⟩ (阶 2) ⊂ ⟨α⟩ (阶 4): 2 ∣ 4
2-divides-4 : 2 ∣ 4
2-divides-4 = divides 2 refl  -- 4 = 2 × 2

-- ⟨α⟩ (阶 4) ⊂ ⟨φ⟩ (阶 8): 4 ∣ 8
4-divides-8 : 4 ∣ 8
4-divides-8 = divides 2 refl  -- 8 = 4 × 2

-- 传递: 2 ∣ 8 (⟨-1⟩ ⊂ ⟨φ⟩)
2-divides-8 : 2 ∣ 8
2-divides-8 = divides 4 refl  -- 8 = 2 × 4

-- 0 postulate.
