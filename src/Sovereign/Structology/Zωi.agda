{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.Zωi
-- Z[ω,i] 环: 2·A₄ = SL(2,3) 二维不可约表示的忠实环 (0 postulate)
--
-- 为什么需要 i: Z[ω] 只有 3 阶元素 (ω³=1), 但 2·A₄ 的二维表示需要 4 阶元素
-- (四元数单位 i,j,k)。二元四面体群的二维矩阵元素含 i, 迹却消去 i 落在 Z[ω]。
-- 因此深度证明的基环必须扩展为 Z[ω,i], 其中 i²=-1, ωi=iω。
--
-- 元素: a + bω + ci + dωi  (a,b,c,d ∈ ℤ)
-- 关系: ω² = -1-ω,  i² = -1,  ωi = iω,  (ωi)² = 1+ω
--
-- 乘法系数 (手工展开 + Python 穷举验证: 恒等式全过, 结合律 20 万组通过):
--   (a+bω+ci+dωi)(a′+b′ω+c′i+d′ωi)
--     = (aa′−bb′−cc′+dd′)
--     + (ab′+ba′−bb′−cd′−dc′+dd′)ω
--     + (ac′+ca′−bd′−db′)i
--     + (ad′+da′+bc′+cb′−bd′−db′)ωi
--
-- 注意: 本模块定义前, 初稿公式有两处错误 (ω 系数漏 +dd′, i 系数符号反),
-- 已由穷举反例 (ωi)²≠1+ω 与结合律反例否决并修正。此为「先算后写」纪律。

module Sovereign.Structology.Zωi where

open import Data.Integer.Base using (ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

--------------------------------------------------------------------------------
-- 1. Z[ω,i] 元素
--------------------------------------------------------------------------------

record Zωi : Set where
  constructor mkZωi
  field
    a : ℤ   -- 常数项系数
    b : ℤ   -- ω 系数
    c : ℤ   -- i 系数
    d : ℤ   -- ωi 系数

open Zωi

zeroZωi : Zωi
zeroZωi = mkZωi (+ 0) (+ 0) (+ 0) (+ 0)

oneZωi : Zωi
oneZωi = mkZωi (+ 1) (+ 0) (+ 0) (+ 0)

ωZωi : Zωi
ωZωi = mkZωi (+ 0) (+ 1) (+ 0) (+ 0)

iZωi : Zωi
iZωi = mkZωi (+ 0) (+ 0) (+ 1) (+ 0)

ωiZωi : Zωi
ωiZωi = mkZωi (+ 0) (+ 0) (+ 0) (+ 1)

--------------------------------------------------------------------------------
-- 2. 加法 / 负元 / 减法
--------------------------------------------------------------------------------

addZωi : Zωi → Zωi → Zωi
addZωi (mkZωi a b c d) (mkZωi a′ b′ c′ d′) =
  mkZωi (a + a′) (b + b′) (c + c′) (d + d′)

negZωi : Zωi → Zωi
negZωi (mkZωi a b c d) = mkZωi (- a) (- b) (- c) (- d)

subZωi : Zωi → Zωi → Zωi
subZωi x y = addZωi x (negZωi y)

--------------------------------------------------------------------------------
-- 3. 乘法 (Python 穷举验证过的公式)
--------------------------------------------------------------------------------

mulZωi : Zωi → Zωi → Zωi
mulZωi (mkZωi a b c d) (mkZωi a′ b′ c′ d′) =
  mkZωi
    (a * a′ - b * b′ - c * c′ + d * d′)
    (a * b′ + b * a′ - b * b′ - c * d′ - d * c′ + d * d′)
    (a * c′ + c * a′ - b * d′ - d * b′)
    (a * d′ + d * a′ + b * c′ + c * b′ - b * d′ - d * b′)

--------------------------------------------------------------------------------
-- 4. 核心恒等式 (全 refl, 具体 ℤ 常数运算归约)
--------------------------------------------------------------------------------

-- ω² = -1 - ω
omega-squared : mulZωi ωZωi ωZωi ≡ addZωi (negZωi oneZωi) (negZωi ωZωi)
omega-squared = refl

-- ω² + ω + 1 = 0
omega-sum-zero : addZωi (addZωi (mulZωi ωZωi ωZωi) ωZωi) oneZωi ≡ zeroZωi
omega-sum-zero = refl

-- i² = -1
i-squared : mulZωi iZωi iZωi ≡ negZωi oneZωi
i-squared = refl

-- i² + 1 = 0
i-squared-zero : addZωi (mulZωi iZωi iZωi) oneZωi ≡ zeroZωi
i-squared-zero = refl

-- ωi = iω (交换)
omega-i-comm : mulZωi ωZωi iZωi ≡ mulZωi iZωi ωZωi
omega-i-comm = refl

-- (ωi)² = 1 + ω
omegai-squared : mulZωi ωiZωi ωiZωi ≡ addZωi oneZωi ωZωi
omegai-squared = refl

-- 0 postulate.
