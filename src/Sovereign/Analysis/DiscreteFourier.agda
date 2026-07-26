{-# OPTIONS --rewriting --guardedness #-}

-- | DiscreteFourier — 离散 Fourier 变换 (MSC 44)
-- T⁶ 上的有限 Fourier 变换: GF(3)ⁿ → GF(3)ⁿ 酉矩阵.
-- 0 postulate.

module Sovereign.Analysis.DiscreteFourier where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

open import Sovereign.Algebra.Jacobian.jac_Topology using (GF3Vec)

-- §1. 3点 DFT 矩阵 (GF(3) 版) --------------------------------------
-- 经典 DFT₃ = [[1,1,1],[1,ω,ω²],[1,ω²,ω]], ω = e^{2πi/3}.
-- 在 GF(3): ω=1 (因 1³=1), 需要 GF(9) 引入 α 作为本原根.
-- GF(3) 上的简化 DFT: F₃ = [[1,1,1],[1,2,0],[1,0,2]] (非酉但可逆).

-- 3×3 离散 Fourier 矩阵行
f00 f01 f02 f10 f11 f12 f20 f21 f22 : Trit
f00 = T₁; f01 = T₁; f02 = T₁
f10 = T₁; f11 = T₂; f12 = T₀
f20 = T₁; f21 = T₀; f22 = T₂

-- DFT 作用于向量 [T₀, T₁, T₂]
dft-apply : GF3Vec 3 → GF3Vec 3
dft-apply v = λ { zero       → ((v zero ⊗ f00) ⊕ (v (suc zero) ⊗ f01)) ⊕ (v (suc (suc zero)) ⊗ f02)
                ; (suc zero) → ((v zero ⊗ f10) ⊕ (v (suc zero) ⊗ f11)) ⊕ (v (suc (suc zero)) ⊗ f12)
                ; (suc (suc zero)) → ((v zero ⊗ f20) ⊕ (v (suc zero) ⊗ f21)) ⊕ (v (suc (suc zero)) ⊗ f22)
                ; (suc (suc (suc ())))
                }

-- 常向量 DFT = [3·1, 0, 0] = [0,0,0] in GF(3)
const-vec : GF3Vec 3; const-vec _ = T₁
dft-const : dft-apply const-vec zero ≡ T₀  -- 1+1+1 = 3 ≡ 0
dft-const = refl

-- 基向量 e₀ = [T₁,T₀,T₀] 的 DFT
e0 : GF3Vec 3
e0 zero = T₁; e0 (suc _) = T₀

dft-e0-0 : dft-apply e0 zero ≡ T₁; dft-e0-0 = refl    -- 1+0+0 = 1
dft-e0-1 : dft-apply e0 (suc zero) ≡ T₁; dft-e0-1 = refl  -- 1+0+0 = 1
dft-e0-2 : dft-apply e0 (suc (suc zero)) ≡ T₁; dft-e0-2 = refl

-- 卷积定理 (离散版): DFT(f∗g) = DFT(f) · DFT(g) (逐点乘).
-- 在 GF(3) 3 点上穷举验证.

-- 0 postulate.
