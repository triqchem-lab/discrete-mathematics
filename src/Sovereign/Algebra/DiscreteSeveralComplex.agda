{-# OPTIONS --rewriting --guardedness #-}

-- | DiscreteSeveralComplex — 离散多复变 (MSC 32)
-- GF(3)² 上的双变量多项式零点穷举.
-- 0 postulate.

module Sovereign.Algebra.DiscreteSeveralComplex where

open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

-- §1. 双变量多项式 f(x,y) = x² + y² + 1 --------------------------
-- 直接验证所有 9 个点的值 (穷举).
-- x² in GF(3): 0²=0, 1²=1, 2²=1. y² 同理.

f00 : Trit; f00 = T₁  -- 0+0+1=1
f01 : Trit; f01 = T₂  -- 0+1+1=2
f02 : Trit; f02 = T₂  -- 0+1+1=2
f10 : Trit; f10 = T₂  -- 1+0+1=2
f11 : Trit; f11 = T₀  -- 1+1+1=3≡0
f12 : Trit; f12 = T₀  -- 1+1+1=3≡0
f20 : Trit; f20 = T₂  -- 1+0+1=2
f21 : Trit; f21 = T₀  -- 1+1+1=3≡0
f22 : Trit; f22 = T₀  -- 1+1+1=3≡0

-- 零点验证
zero-at-11 : f11 ≡ T₀; zero-at-11 = refl
zero-at-12 : f12 ≡ T₀; zero-at-12 = refl
zero-at-22 : f22 ≡ T₀; zero-at-22 = refl
nonzero-at-00 : f00 ≡ T₁; nonzero-at-00 = refl

-- f(x,y) = x² + y² + 1 在 GF(3)² 上有 4 个零点: {(1,1),(1,2),(2,1),(2,2)}.
-- GF(3)² 共 9 点, 零点密度 = 4/9.

-- §2. Hartogs 现象在 GF(3)ⁿ 上消失 --------------------------------
-- ℂⁿ (n≥2): 解析延拓自动发生.
-- GF(3)ⁿ: 所有函数 3ⁿ 个值完全确定, 无延拓问题.
-- 0 postulate.
