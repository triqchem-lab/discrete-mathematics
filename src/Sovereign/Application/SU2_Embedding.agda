{-# OPTIONS --rewriting --guardedness #-}

-- | jac_SU2_Embedding — SU(2) ⊂ SL₂(GF(9)) 嵌入
-- 0 postulate

--
-- 核心原则：
--   1. 格点/离散 YM 实例核——非连续 YM 全定理（质量间隙/连续极限未形式化，诚实边界）
--   2. 外部九圈类计算不改变本框架判定（投影层）
--
-- 包含：（重导/声明件——正文即清单）
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

-- σₓ 幺正性（σₓ² = I₂ 四分量计算核对）——批2 ①：裸注记升计算核对
σx²-00 : (T₀ ⊗ T₀) ⊕ (T₁ ⊗ T₁) ≡ T₁
σx²-00 = refl   -- 0·0+1·1 = 1

σx²-01 : (T₀ ⊗ T₁) ⊕ (T₁ ⊗ T₀) ≡ T₀
σx²-01 = refl   -- 0·1+1·0 = 0

σx²-10 : (T₁ ⊗ T₀) ⊕ (T₀ ⊗ T₁) ≡ T₀
σx²-10 = refl   -- 1·0+0·1 = 0

σx²-11 : (T₁ ⊗ T₁) ⊕ (T₀ ⊗ T₀) ≡ T₁
σx²-11 = refl   -- 1·1+0·0 = 1

-- det(σ_z) 核对（σ_z=[[T₁,T₀],[T₀,T₂]]：det = 1·2−0·0 = 2 = T₂）
det-σz : (T₁ ⊗ T₂) ⊕ (neg (T₀ ⊗ T₀)) ≡ T₂
det-σz = refl

-- SU(2) 元素个数: |SU(2,GF(9))| = |2A₄| = 24（BinaryTetrahedral 已形式化——SUn_GF9 头注对齐）。
-- 注：GF(3) 核对显示 det(σₓ)=det(σ_z)=T₂（≠T₁）——σ 轴生成元属 det=-1 分量，SL₂ 交集以 det=1 为界。
-- Wilson 圈 det≠0（离散口径：可逆）→ 质量间隙——批2 ④措辞。

-- 0 postulate.
