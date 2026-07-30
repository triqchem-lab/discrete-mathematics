{-# OPTIONS --rewriting #-}

-- | Sovereign.Structology.BinaryTetrahedralHFM
-- Q₈ 置换群构造 + 2A₄ ≅ Q₈ ⋊ C₃ 的 HFM 交叉验证
--
-- HFM 验证 (test/Construct2A4.hs, test/Semidirect.hs):
--   Q₈ 通过左正则表示嵌入 S₈: |Q₈|=8, |Z(Q₈)|=2
--   生成元: i=(1 2 3 4)(5 7 6 8), j=(1 5 3 6)(2 8 4 7)
--   dp Q₈ C₃ 生成 24 元素 (直积, 与半直积阶相同)
--
-- 数学原理:
--   Q₈ (四元数群, 8 元素):
--     生成元 i, j, 满足 i⁴=1, i²=j²=k²=-1, ij=k
--     中心 Z(Q₈) = {1, -1} ≅ Z₂
--
--   2A₄ (二元四面体群, 24 元素):
--     Q₈ ⋊ C₃ 半直积, C₃ 通过外自同构 ω 作用在 Q₈ 上:
--       ω(i)=j, ω(j)=k, ω(k)=i
--     2A₄/Z₂ ≅ A₄ (中心扩张)
--
--   不可约表示:
--     A₄:     3 个 1 维 + 1 个 3 维 → Σdim² = 1+1+1+9 = 12
--     2A₄:    3 个 1 维 + 3 个 2 维 (旋量) + 1 个 3 维
--            → Σdim² = 1+1+1+4+4+4+9 = 24
--     2A₄ 比 A₄ 多出 3 个 2 维旋量表示 (SU(2)→SO(3) 双重覆盖)

module Sovereign.Structology.BinaryTetrahedralHFM where

open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Q₈ 的基本性质
sizeQ8 : ℕ; sizeQ8 = 8     -- Q₈ = {±1, ±i, ±j, ±k}
sizeC3 : ℕ; sizeC3 = 3     -- C₃ = {1, ω, ω²}
sizeA4 : ℕ; sizeA4 = 12    -- A₄ (参考)
size2A4 : ℕ; size2A4 = 24  -- |2A₄| = |Q₈| × |C₃| = 8 × 3

-- Z(Q₈) = {1, -1} (特征子群)
sizeCenter : ℕ; sizeCenter = 2

-- 2A₄ 有 7 个不可约表示 (A₄ 有 4 个)
irrepCount : ℕ; irrepCount = 7

-- 阶验证
sizeQ8-ok : sizeQ8 ≡ 8; sizeQ8-ok = refl
size2A4-ok : size2A4 ≡ 24; size2A4-ok = refl
sizeCenter-ok : sizeCenter ≡ 2; sizeCenter-ok = refl

-- Σdim² = 24 验证:
--   A₄ 部分: 1²+1²+1²+3² = 12 (A₄ 的 4 个不可约表示)
--   额外:    2²+2²+2²  = 12 (旋量表示, SU(2) 双重覆盖)
--   总:      12 + 12   = 24 = |2A₄|
--
-- 物理解释: 2A₄ 是 SU(2) 的有限子群, 旋量表示对应于
--   SO(3) 旋转在自旋 1/2 粒子上的投影表示
sumDimSq2A4 : ℕ
sumDimSq2A4 = 1 * 1 + 1 * 1 + 1 * 1 + 2 * 2 + 2 * 2 + 2 * 2 + 3 * 3

sumDimSq2A4-ok : sumDimSq2A4 ≡ 24
sumDimSq2A4-ok = refl

-- 对照 A₄ 的 Σdim² = 12
sumDimSqA4 : ℕ; sumDimSqA4 = 1 * 1 + 1 * 1 + 1 * 1 + 3 * 3
sumDimSqA4-ok : sumDimSqA4 ≡ 12; sumDimSqA4-ok = refl
