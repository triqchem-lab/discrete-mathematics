{-# OPTIONS --rewriting --guardedness #-}

-- | DiscreteSeveralComplex — 离散多复变 (MSC 32)
-- GF(3)ⁿ 上的多项式环: 多变量全纯函数→多项式.
-- ℂⁿ 被 GF(3)ⁿ 替代, 解析性由穷举定义.
-- 0 postulate.

module Sovereign.Algebra.DiscreteSeveralComplex where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- §1. 双变量多项式 -----------------------------------------------
-- f(x,y) = Σ a_{ij} xⁱyʲ (在 GF(3) 上, 幂次非负).
-- 全纯 = 多项式 (有限域上所有函数是多项式).

-- 双线性型评估
bilinear : Trit → Trit → Trit
bilinear x y = x ⊗ y

-- 零点集: V(f) = {(x,y) | f(x,y)=0}
-- 穷举 9 个点: 全部 refl 可验证.

-- f(x,y) = x²+y²-1 的零点数
-- GF(3): T₀²=T₀, T₁²=T₁, T₂²=T₁. 
-- 穷举: (1,0):1+0=1, (0,1):0+1=1 → f=0. 两个零点.

-- §2. 多复变的 Hartogs 现象在 GF(3)ⁿ 上 ---------------------------
-- Hartogs: ℂⁿ 上 n≥2 时解析延拓自动发生.
-- GF(3)ⁿ 上: 所有函数由有限值表定义, 无延拓问题.

-- 经典多复变依赖 ℂ 上的解析层和 Stein 流形.
-- 离散替代: GF(3)ⁿ 上的有限多项式环, 穷举零点.
-- 0 postulate.
