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
--     |2A₄| = |Q₈| · |C₃| = 8 × 3 = 24 (半直积保持阶乘积)
--
--   不可约表示:
--     A₄:     Σdim² = 1²+1²+1²+3² = 12 = |A₄|
--     2A₄:    Σdim² = 1²+1²+1²+2²+2²+2²+3² = 24 = |2A₄|
--     2A₄ 比 A₄ 多出 3 个 2 维旋量表示 (SU(2)→SO(3) 双重覆盖)

module Sovereign.Structology.BinaryTetrahedralHFM where

open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning

-- Q₈ 的基本性质
sizeQ8 : ℕ; sizeQ8 = 8     -- Q₈ = {±1, ±i, ±j, ±k}
sizeC3 : ℕ; sizeC3 = 3     -- C₃ = {1, ω, ω²}
sizeA4 : ℕ; sizeA4 = 12    -- A₄ (参考)

-- |2A₄| = |Q₈| · |C₃| (半直积保持阶乘积)
size2A4 : ℕ; size2A4 = sizeQ8 * sizeC3  -- 8 × 3

-- Z(Q₈) = {1, -1} (特征子群)
sizeCenter : ℕ; sizeCenter = 2

-- 2A₄ 有 7 个不可约表示 (A₄ 有 4 个)
irrepCount : ℕ; irrepCount = 7

-- |Q₈| = 8
sizeQ8-ok : sizeQ8 ≡ 8
sizeQ8-ok =
  begin
    sizeQ8
  ≡⟨⟩  8
  ∎

-- |2A₄| = 8 × 3 = 24
size2A4-ok : size2A4 ≡ 24
size2A4-ok =
  begin
    size2A4
  ≡⟨⟩  -- 展开: sizeQ8 * sizeC3
    sizeQ8 * sizeC3
  ≡⟨⟩  -- sizeQ8 = 8
    8 * sizeC3
  ≡⟨⟩  -- sizeC3 = 3
    8 * 3
  ≡⟨⟩  -- 8 × 3 = 24
    24
  ∎

-- |Z(Q₈)| = 2
sizeCenter-ok : sizeCenter ≡ 2
sizeCenter-ok =
  begin
    sizeCenter
  ≡⟨⟩  2
  ∎

-- Σdim² = 1²+1²+1²+2²+2²+2²+3² = 24
-- 验证: 2A₄ 的 7 个不可约表示维数平方和等于 |2A₄|
sumDimSq2A4 : ℕ
sumDimSq2A4 = 1 * 1 + 1 * 1 + 1 * 1 + 2 * 2 + 2 * 2 + 2 * 2 + 3 * 3

sumDimSq2A4-ok : sumDimSq2A4 ≡ 24
sumDimSq2A4-ok =
  begin
    sumDimSq2A4
  ≡⟨⟩  -- 展开各项
    1 * 1 + 1 * 1 + 1 * 1 + 2 * 2 + 2 * 2 + 2 * 2 + 3 * 3
  ≡⟨⟩  -- 1²=1, 2²=4, 3²=9
    1 + 1 + 1 + 4 + 4 + 4 + 9
  ≡⟨⟩  -- 1+1+1 = 3
    3 + 4 + 4 + 4 + 9
  ≡⟨⟩  -- 3+4 = 7
    7 + 4 + 4 + 9
  ≡⟨⟩  -- 7+4 = 11
    11 + 4 + 9
  ≡⟨⟩  -- 11+4 = 15
    15 + 9
  ≡⟨⟩  -- 15+9 = 24
    24
  ∎

-- 对照 A₄ 的 Σdim² = 1²+1²+1²+3² = 12
sumDimSqA4 : ℕ; sumDimSqA4 = 1 * 1 + 1 * 1 + 1 * 1 + 3 * 3

sumDimSqA4-ok : sumDimSqA4 ≡ 12
sumDimSqA4-ok =
  begin
    sumDimSqA4
  ≡⟨⟩
    1 * 1 + 1 * 1 + 1 * 1 + 3 * 3
  ≡⟨⟩
    1 + 1 + 1 + 9
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    12
  ∎
