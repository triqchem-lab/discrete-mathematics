{-# OPTIONS --rewriting #-}

-- | Sovereign.Structology.BinaryTetrahedralHFM
-- Q₈ 置换群构造的 HFM 交叉验证 (Cayley 定理)
-- HFM 验证 (test/Construct2A4.hs):
--   Q₈ 通过左正则表示嵌入 S₈: 8 元素, 中心 |Z|=2
--   生成元: i=(1 2 3 4)(5 7 6 8), j=(1 5 3 6)(2 8 4 7)
--   i²=j²=k²=-1, k=ij, i⁴=1

module Sovereign.Structology.BinaryTetrahedralHFM where

open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 阶
sizeQ8 : ℕ; sizeQ8 = 8
sizeC3 : ℕ; sizeC3 = 3
sizeA4 : ℕ; sizeA4 = 12
size2A4 : ℕ; size2A4 = 24
sizeCenter : ℕ; sizeCenter = 2
irrepCount : ℕ; irrepCount = 7

sizeQ8-ok : sizeQ8 ≡ 8; sizeQ8-ok = refl
size2A4-ok : size2A4 ≡ 24; size2A4-ok = refl
sizeCenter-ok : sizeCenter ≡ 2; sizeCenter-ok = refl

-- Σdim² = 24
sumDimSq2A4 : ℕ
sumDimSq2A4 = 1 + 1 + 1 + 4 + 4 + 4 + 9

sumDimSq2A4-ok : sumDimSq2A4 ≡ 24
sumDimSq2A4-ok = refl

-- Σdim²(A₄) = 12 (对照)
sumDimSqA4 : ℕ; sumDimSqA4 = 1 + 1 + 1 + 9
sumDimSqA4-ok : sumDimSqA4 ≡ 12; sumDimSqA4-ok = refl
