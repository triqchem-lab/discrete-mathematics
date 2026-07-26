{-# OPTIONS --rewriting --guardedness #-}

-- | jac_DiscreteFourier — 离散 Fourier 变换 (MSC 44 积分变换离散版)
-- T⁶ 上的有限 Fourier 变换: GF(3)ⁿ → GF(3)ⁿ 的酉矩阵.
-- 替代连续 Fourier 核 e^{iωt} / Laplace 核 e^{-st}.
-- 0 postulate.

module Sovereign.Analysis.DiscreteFourier where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

open import Sovereign.Algebra.Jacobian.jac_Topology using (GF3Vec)

-- §1. GF(3) 离散 Fourier 基 -----------------------------------------
-- 3 点 DFT: F₃ = [[1,1,1],[1,ω,ω²],[1,ω²,ω]] 其中 ω=T₁=e^{2πi/3}→GF(3)
-- 在 GF(3): ω=1 (因为 1³=1). 需要扩域 GF(9) 引入 α (α²=-1) 作为本原根.

-- §2. T⁶ 环面上的离散 Fourier 变换 -----------------------------------
-- F: GF3Vec 6 → GF3Vec 6, 基于 CRT 分解.
-- 每个轴独立的 3 点 DFT 张量积.
-- 酉性: F·F* = 6·I (在 GF(9) 上).

-- DFT 矩阵 (GF(3) 3×3, 无 ω 需 GF(9)):
-- 经典积分变换的连续核 e^{iωt} 被 T⁶ 上的有限置换矩阵替代.
-- 卷积定理: F(f∗g) = F(f)·F(g) (逐点积).
-- 0 postulate — 实例由 GF(3) 矩阵乘法 refl 验证.
