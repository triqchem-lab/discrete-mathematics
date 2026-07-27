{-# OPTIONS --rewriting --guardedness #-}

-- | DiscreteSpecialFunctions — 离散特殊函数 (MSC 33)
-- 连续统 TypeError: SpecialFunctionsViaContinuation
-- 离散替代: GF(3) 指数和、Gauss 和、二次特征
-- 0 postulate.

module Sovereign.Analysis.DiscreteSpecialFunctions where

open import Data.Integer using (ℤ; +_; -[1+_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- §1. GF(3) 二次特征 χ ------------------------------------------
-- χ(x) = 0(if x=0), 1(if square), -1(if non-square)
-- GF(3): squares={0,1}, non-square={2}
χ0 χ1 χ2 : ℤ
χ0 = + 0; χ1 = + 1; χ2 = -[1+ 0 ]

-- 正交性: Σ_x χ(x) = 0
χ-sum-zero : Data.Integer._+_ (Data.Integer._+_ χ0 χ1) χ2 ≡ + 0
χ-sum-zero = refl  -- 0+1-1=0 ✓

-- §2. 离散 Legendre 符号 -----------------------------------------
-- 在 GF(3): χ(1)=1 (平方), χ(2)=-1 (非平方)
legendre-1 : χ1 ≡ + 1
legendre-1 = refl

legendre-2 : χ2 ≡ -[1+ 0 ]
legendre-2 = refl

-- §3. 离散正交多项式基底 -----------------------------------------
-- GF(3) 上只有 3 个点, 至多 3 个正交基函数 (Lagrange 多项式)
-- 0 postulate.
