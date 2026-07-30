{-# OPTIONS --rewriting #-}

-- | Sovereign.Structology.MagicSquareHFM
-- M₄ 幻方常数的 HFM 交叉验证
--
-- HFM 验证: test/ExtendedVerify.hs
--
-- 数学原理:
--   Dürer 的 4×4 幻方 (1514 年作品"忧郁"):
--     [16  2  3 13]
--     [ 5 11 10  8]
--     [ 9  7  6 12]
--     [ 4 14 15  1]
--
--   幻方常数 34 的推导:
--     所有 1..16 之和 = 16×17/2 = 136
--     4 行均分: 136/4 = 34
--     同理对角线、列也都等于 34
--
--   与本项目的关系 (ArthurMagicSquare.agda):
--     M₄ 幻方是 T⁶ 格点到 4×4 阵列的正交投影
--     A₄ 群通过 a4ActionOnMatrix 作用在 M₄ 上
--     幻方常数的不变性是 A₄ 作用的直接结果
--     全息 π = 144/46 与 M₄ 的 4×4 结构有关:
--       144 = 12² (十二平均律), 46 = 2×23
--
--   更深层: 144 阶幻方 (MagicSquare144.agda) 是 M₄ 的推广
--     幻方 144 阶: 1+...+144² = 144(144²+1)/2
--     常数 = 144(144²+1)/(2×144) = (144²+1)/2 = 10369

module Sovereign.Structology.MagicSquareHFM where

open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Dürer 幻方 M₄:
--   [16  2  3 13]
--   [ 5 11 10  8]
--   [ 9  7  6 12]
--   [ 4 14 15  1]

-- 行: 16+2+3+13 = 34
row0 : ℕ; row0 = 16 + 2  + 3  + 13
-- 行: 5+11+10+8 = 34
row1 : ℕ; row1 = 5  + 11 + 10 + 8
-- 行: 9+7+6+12 = 34
row2 : ℕ; row2 = 9  + 7  + 6  + 12
-- 行: 4+14+15+1 = 34
row3 : ℕ; row3 = 4  + 14 + 15 + 1

row0-ok : row0 ≡ 34; row0-ok = refl
row1-ok : row1 ≡ 34; row1-ok = refl
row2-ok : row2 ≡ 34; row2-ok = refl
row3-ok : row3 ≡ 34; row3-ok = refl

-- 列: 16+5+9+4 = 34
col0 : ℕ; col0 = 16 + 5 + 9  + 4
-- 列: 2+11+7+14 = 34
col1 : ℕ; col1 = 2  + 11 + 7 + 14
-- 列: 3+10+6+15 = 34
col2 : ℕ; col2 = 3  + 10 + 6 + 15
-- 列: 13+8+12+1 = 34
col3 : ℕ; col3 = 13 + 8  + 12 + 1

col0-ok : col0 ≡ 34; col0-ok = refl
col1-ok : col1 ≡ 34; col1-ok = refl
col2-ok : col2 ≡ 34; col2-ok = refl
col3-ok : col3 ≡ 34; col3-ok = refl

-- 主对角线: 16+11+6+1 = 34
diag1 : ℕ; diag1 = 16 + 11 + 6 + 1
-- 副对角线: 13+10+7+4 = 34
diag2 : ℕ; diag2 = 13 + 10 + 7 + 4

diag1-ok : diag1 ≡ 34; diag1-ok = refl
diag2-ok : diag2 ≡ 34; diag2-ok = refl

-- 幻方常数验证全部通过
-- M₄ 是 4×4 幻方的一个实例, 满足:
--   每行和 = 每列和 = 每条对角线和 = 34
--   幻方常数的通用公式: C = n(n²+1)/2, n=4 → 4×17/2 = 34
