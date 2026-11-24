{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.ZetaFrame
-- zeta 分式的公共类型框架（M1 · A1.7a，自 ZetaFunctional §0 逐字提取）
--
-- 提取理由: ∀ 版（ZetaAllF3，覆盖 18 条曲线）与 3 曲线版（ZetaFunctional）
--   共用同一套多项式/分式机械；提取后两处 import，不再复制 §0。
--   本文件内容与 ZetaFunctional 原 §0 逐字一致：
--   Quad / QuadE / Quart / ZetaFraction、_*q_、recipClear、_*ₖ_、mulLin、
--   embed、negᵉ、evalE、Zpoly、denPoly、Z、numEis、reversePoly。
--   宪法: 无除法——T ↦ 1/qT 以通分多项式 recipClear 表达；分式相等用交叉相乘。
-- 0 postulate。

module Sovereign.Application.Problems.RH.ZetaFrame where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Sovereign.Foundation.Eisenstein
  using (Eisenstein; eis; 1ᵉ; _+ᵉ_; _*ᵉ_)

--------------------------------------------------------------------------------
-- §0. 多项式与分数类型
--------------------------------------------------------------------------------

-- 二次多项式 c0 + c1·T + c2·T² (ℤ 系数)
record Quad : Set where
  constructor quad
  field
    c0 : ℤ
    c1 : ℤ
    c2 : ℤ

-- 二次多项式 (Eisenstein 系数, 用于 (1−αT)(1−βT) 分解)
record QuadE : Set where
  constructor quadE
  field
    e0 : Eisenstein
    e1 : Eisenstein
    e2 : Eisenstein

-- 四次多项式 d0 + d1·T + d2·T² + d3·T³ + d4·T⁴ (交叉相乘产物)
record Quart : Set where
  constructor quart
  field
    d0 d1 d2 d3 d4 : ℤ

-- zeta 分数 Z(T) = num/den
record ZetaFraction : Set where
  constructor frac
  field
    num : Quad
    den : Quad

-- Quad 乘法 → Quart (系数公式, 卷积)
_*q_ : Quad → Quad → Quart
quad a0 a1 a2 *q quad b0 b1 b2 =
  quart (a0 * b0)
        (a0 * b1 + a1 * b0)
        (a0 * b2 + a1 * b1 + a2 * b0)
        (a1 * b2 + a2 * b1)
        (a2 * b2)

-- 通分替换: q²T²·P(1/qT), 即系数 (c0+c1T+c2T²) ↦ (c2 + c1·q·T + c0·q²·T²)
recipClear : ℤ → Quad → Quad
recipClear q (quad c0 c1 c2) = quad c2 (c1 * q) (c0 * q * q)

-- 标量乘
_*ₖ_ : ℤ → Quad → Quad
k *ₖ quad c0 c1 c2 = quad (k * c0) (k * c1) (k * c2)

-- 一次多项式乘法 (a0+a1T)(b0+b1T), 用于分母因式分解
mulLin : ℤ → ℤ → ℤ → ℤ → Quad
mulLin a0 a1 b0 b1 = quad (a0 * b0) (a0 * b1 + a1 * b0) (a1 * b1)

-- ℤ 系数嵌入 Eisenstein 系数
embed : Quad → QuadE
embed (quad c0 c1 c2) = quadE (eis c0 (+ 0)) (eis c1 (+ 0)) (eis c2 (+ 0))

-- Eisenstein 一元负
negᵉ : Eisenstein → Eisenstein
negᵉ (eis a b) = eis (- a) (- b)

-- 多项式求值 (Eisenstein)
evalE : QuadE → Eisenstein → Eisenstein
evalE (quadE c0 c1 c2) x = c0 +ᵉ c1 *ᵉ x +ᵉ c2 *ᵉ x *ᵉ x

-- Z(T) 的分子 L(T) = 1 − tT + qT²
Zpoly : ℤ → ℤ → Quad
Zpoly t q = quad (+ 1) (- t) q

-- Z(T) 的分母 (1−T)(1−qT) = (qT−1)(T−1) = 1 − (1+q)T + qT² (展开式)
denPoly : ℤ → Quad
denPoly q = quad (+ 1) (- (+ 1 + q)) q

-- Z(T) = L(T)/((1−T)(1−qT))
Z : ℤ → ℤ → ZetaFraction
Z t q = frac (Zpoly t q) (denPoly q)

-- 分子 (1−αT)(1−βT) 的展开式 (Eisenstein 系数): 1 − (α+β)T + αβ·T²
numEis : Eisenstein → Eisenstein → QuadE
numEis α β = quadE 1ᵉ (negᵉ (α +ᵉ β)) (α *ᵉ β)

-- 互逆多项式 P*(T) = T²·P(1/T) = (T−α)(T−β) = T² − tT + q
reversePoly : ℤ → ℤ → Quad
reversePoly t q = quad q (- t) (+ 1)
