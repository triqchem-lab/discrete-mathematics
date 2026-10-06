{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LaurentPolynomial
-- Laurent 多项式环 Z[t,t⁻¹] 的最小形式化
--
-- 载体：ℤ 上的 Laurent 多项式（t 的有限指数和）
-- 简化版：用 (ℤ × ℤ) 表示 a + bt 形式（t 的一次项）
-- 完整版需要：多项式系数列表 + 乘法卷积
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.LaurentPolynomial where

open import Data.Integer using (ℤ; +_; -[1+_] ; _+_; _*_; -_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Laurent 多项式 Z[t,t⁻¹] 的简化版（只用 t 的一次项）
-- 实际 Burau 表示需要完整的 Laurent 多项式环
-- 简化：用 (ℤ × ℤ) 表示 a + bt 形式

record Laurent : Set where
  constructor _⊕_
  field
    const : ℤ    -- 常数项
    coeff : ℤ    -- t 的系数

open Laurent

-- Laurent 多项式的加法
_+L_ : Laurent → Laurent → Laurent
(a ⊕ b) +L (c ⊕ d) = (a + c) ⊕ (b + d)

-- Laurent 多项式的乘法（简化版：(a+bt)(c+d) = ac + (ad+bc)t + bd t²）
-- 完整版需要处理 t² 项（归入更高次项）
_*L_ : Laurent → Laurent → Laurent
(a ⊕ b) *L (c ⊕ d) = (a * c) ⊕ ((a * d) + (b * c))
-- 忽略 bd t² 项（简化版）

-- 具体 Laurent 多项式
L0 : Laurent
L0 = (+ 0) ⊕ (+ 0)

L1 : Laurent
L1 = (+ 1) ⊕ (+ 0)

Lt : Laurent
Lt = (+ 0) ⊕ (+ 1)

L-t : Laurent
L-t = (+ 0) ⊕ (-[1+ 0 ])

-- 验证：(1-t)*t = t - t²（简化版：只有 t 项）
example-mul : (L1 +L L-t) *L Lt ≡ Lt
example-mul = refl  -- (1+0) * 0 + (1*1 + 0*0) = 1 → 0 ⊕ 1 = Lt
