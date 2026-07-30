{-# OPTIONS --rewriting #-}

-- | Sovereign.Structology.MagicSquareHFM
-- M₄ 幻方常数的 HFM 交叉验证 (test/ExtendedVerify.hs)
--   Dürer 的 4×4 幻方: 行/列/对角线和 = 34

module Sovereign.Structology.MagicSquareHFM where

open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 幻方常数
magicConstant : ℕ; magicConstant = 34

-- 4×4 幻方 (Dürer, 1514)
-- 行
row0 : ℕ; row0 = 16 + 2  + 3  + 13
row1 : ℕ; row1 = 5  + 11 + 10 + 8
row2 : ℕ; row2 = 9  + 7  + 6  + 12
row3 : ℕ; row3 = 4  + 14 + 15 + 1

row0-ok : row0 ≡ 34; row0-ok = refl
row1-ok : row1 ≡ 34; row1-ok = refl
row2-ok : row2 ≡ 34; row2-ok = refl
row3-ok : row3 ≡ 34; row3-ok = refl

-- 列
col0 : ℕ; col0 = 16 + 5 + 9  + 4
col1 : ℕ; col1 = 2  + 11 + 7 + 14
col2 : ℕ; col2 = 3  + 10 + 6 + 15
col3 : ℕ; col3 = 13 + 8  + 12 + 1

col0-ok : col0 ≡ 34; col0-ok = refl
col1-ok : col1 ≡ 34; col1-ok = refl
col2-ok : col2 ≡ 34; col2-ok = refl
col3-ok : col3 ≡ 34; col3-ok = refl

-- 对角线
diag1 : ℕ
diag1 = 16 + 11 + 6 + 1

diag2 : ℕ
diag2 = 13 + 10 + 7 + 4

diag1-ok : diag1 ≡ 34; diag1-ok = refl
diag2-ok : diag2 ≡ 34; diag2-ok = refl
