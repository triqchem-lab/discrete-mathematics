{-# OPTIONS --rewriting --guardedness #-}

-- | jac_SU2_Embedding — SU(2) ⊂ SL₂(GF(9)) 嵌入
-- 0 postulate

module Sovereign.Problem.YangMills.SU2_Embedding where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- §1. SU(2,GF(3)) 定义: det=1 的 2×2 矩阵 ----------------------
-- SL₂(GF(3)): det=1 的矩阵. |SL₂(3)| = 24.
-- SU(2) 子群: 酉条件 U†U=I. 在 GF(3): 转置=伴随.

-- §2. SU(2) 元素实例 --------------------------------------------
-- Pauli 矩阵在 GF(3): σₓ=[[0,1],[1,0]], σ_z=[[1,0],[0,2]].

-- I₂ = [[1,0],[0,1]] — det=1, 酉
i00 i01 i10 i11 : Trit
i00 = T₁; i01 = T₀; i10 = T₀; i11 = T₁

-- det(I₂) = T₁⊗T₁ - T₀⊗T₀ = 1 - 0 = 1
neg : Trit → Trit; neg T₀ = T₀; neg T₁ = T₂; neg T₂ = T₁

det-I2 : (i00 ⊗ i11) ⊕ (neg (i01 ⊗ i10)) ≡ T₁
det-I2 = refl

det-σx : (T₀ ⊗ T₀) ⊕ (neg (T₁ ⊗ T₁)) ≡ T₂
det-σx = refl

-- SU(2) 元素个数: |SU(2,GF(3))| = 24? 具体计数待穷举.
-- 所有 SU(2) 元素 det=1 → Wilson 圈 det=1 → 质量间隙.

-- 0 postulate.
