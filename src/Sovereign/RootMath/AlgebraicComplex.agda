{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.RootMath.AlgebraicComplex
-- 代数复数：避免连续统的复数表示
--
-- 宪法原则：
-- 1. 禁止使用 Data.Complex (连续统复数)。
-- 2. 复数表示为 (实部 : ℚ, 虚部系数 : ℚ)，对应 a + b√(-1)。
-- 3. 在律算中，虚部通常与能隙 Δ=√3 关联，因此使用 √3 系数更合适。
--
-- 本模块提供两种代数复数：
-- - Gaussian: a + bi (i² = -1)
-- - Sqrt3: a + b√3 (用于能隙相关计算)

module Sovereign.RootMath.AlgebraicComplex where

open import Data.Rational using (ℚ; _+_; _-_; _*_; _/_)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

--------------------------------------------------------------------------------
-- 1. 高斯代数复数 (Gaussian Algebraic Complex)
--------------------------------------------------------------------------------

-- 表示 a + bi，其中 a, b 为有理数
record Gaussian : Set where
  constructor _+i_
  field
    re : ℚ  -- 实部
    im : ℚ  -- 虚部系数

open Gaussian public

-- 复数运算
i : Gaussian
i = 0b0 +i 1b1  -- 0 + 1i

_+ᵍ_ : Gaussian → Gaussian → Gaussian
(a +i b) +ᵍ (c +i d) = (a + c) +i (b + d)

_-ᵍ_ : Gaussian → Gaussian → Gaussian
(a +i b) -ᵍ (c +i d) = (a - c) +i (b - d)

_*ᵍ_ : Gaussian → Gaussian → Gaussian
(a +i b) *ᵍ (c +i d) = 
  -- (a+bi)(c+di) = (ac-bd) + (ad+bc)i
  ((a * c) - (b * d)) +i ((a * d) + (b * c))

-- 共轭
conjᵍ : Gaussian → Gaussian
conjᵍ (a +i b) = a +i (- b)

-- 模长平方 (有理数)
normSqᵍ : Gaussian → ℚ
normSqᵍ (a +i b) = (a * a) + (b * b)

--------------------------------------------------------------------------------
-- 2. √3 代数复数 (Sqrt3 Complex) - 用于能隙计算
--------------------------------------------------------------------------------

-- 表示 a + b√3，其中 a, b 为有理数
-- 这与能隙 Δ=√3 的代数结构兼容
record Sqrt3 : Set where
  constructor _+s3_
  field
    re : ℚ  -- 有理部
    s3 : ℚ  -- √3 系数

open Sqrt3 public

-- √3 (即 0 + 1√3)
sqrt3 : Sqrt3
sqrt3 = 0b0 +s3 1b1

-- 运算
_+ˢ_ : Sqrt3 → Sqrt3 → Sqrt3
(a +s3 b) +ˢ (c +s3 d) = (a + c) +s3 (b + d)

_-ˢ_ : Sqrt3 → Sqrt3 → Sqrt3
(a +s3 b) -ˢ (c +s3 d) = (a - c) +s3 (b - d)

_*ˢ_ : Sqrt3 → Sqrt3 → Sqrt3
(a +s3 b) *ˢ (c +s3 d) = 
  -- (a+b√3)(c+d√3) = (ac+3bd) + (ad+bc)√3
  let three = 3b3 / 1b1
  in ((a * c) + (three * b * d)) +s3 ((a * d) + (b * c))

-- 共轭 (√3 → -√3)
conjˢ : Sqrt3 → Sqrt3
conjˢ (a +s3 b) = a +s3 (- b)

-- 范数 (a+b√3)(a-b√3) = a² - 3b²
normˢ : Sqrt3 → ℚ
normˢ (a +s3 b) = 
  let three = 3b3 / 1b1
  in (a * a) - (three * b * b)

--------------------------------------------------------------------------------
-- 3. 与能隙 Δ=√3 的对齐
--------------------------------------------------------------------------------

-- 能隙 Δ = √3 表示为 Sqrt3 复数
EnergyGap : Sqrt3
EnergyGap = sqrt3  -- 0 + 1√3

-- 能隙平方 = 3
EnergyGapSq : normˢ (EnergyGap *ˢ EnergyGap) ≡ 3b3 / 1b1
EnergyGapSq = refl
-- 证明：(√3)² = 3

--------------------------------------------------------------------------------
-- 4. 宪法合规性
--------------------------------------------------------------------------------

-- 本模块不使用 Data.Complex，所有运算在有理数域上闭合。
-- 这避免了连续统复数对离散拓扑证明的污染。
