{-# OPTIONS --rewriting #-}

-- | Sovereign.Structology.MagicSquareHFM
-- M4 幻方常数的 HFM 交叉验证

module Sovereign.Structology.MagicSquareHFM where

open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning

-- Durer 4x4: [16 2 3 13; 5 11 10 8; 9 7 6 12; 4 14 15 1]

-- 行
row0 : ℕ; row0 = 16 + 2  + 3  + 13
row0-ok : row0 ≡ 34
row0-ok = begin row0 ≡⟨⟩ 16 + 2 + 3 + 13 ≡⟨⟩ 18 + 3 + 13 ≡⟨⟩ 21 + 13 ≡⟨⟩ 34 ∎

row1 : ℕ; row1 = 5  + 11 + 10 + 8
row1-ok : row1 ≡ 34
row1-ok = begin row1 ≡⟨⟩ 5 + 11 + 10 + 8 ≡⟨⟩ 16 + 10 + 8 ≡⟨⟩ 26 + 8 ≡⟨⟩ 34 ∎

row2 : ℕ; row2 = 9  + 7  + 6  + 12
row2-ok : row2 ≡ 34
row2-ok = begin row2 ≡⟨⟩ 9 + 7 + 6 + 12 ≡⟨⟩ 16 + 6 + 12 ≡⟨⟩ 22 + 12 ≡⟨⟩ 34 ∎

row3 : ℕ; row3 = 4  + 14 + 15 + 1
row3-ok : row3 ≡ 34
row3-ok = begin row3 ≡⟨⟩ 4 + 14 + 15 + 1 ≡⟨⟩ 18 + 15 + 1 ≡⟨⟩ 33 + 1 ≡⟨⟩ 34 ∎

-- 列
col0 : ℕ; col0 = 16 + 5 + 9  + 4
col0-ok : col0 ≡ 34
col0-ok = begin col0 ≡⟨⟩ 16 + 5 + 9 + 4 ≡⟨⟩ 21 + 9 + 4 ≡⟨⟩ 30 + 4 ≡⟨⟩ 34 ∎

col1 : ℕ; col1 = 2  + 11 + 7 + 14
col1-ok : col1 ≡ 34
col1-ok = begin col1 ≡⟨⟩ 2 + 11 + 7 + 14 ≡⟨⟩ 13 + 7 + 14 ≡⟨⟩ 20 + 14 ≡⟨⟩ 34 ∎

col2 : ℕ; col2 = 3  + 10 + 6 + 15
col2-ok : col2 ≡ 34
col2-ok = begin col2 ≡⟨⟩ 3 + 10 + 6 + 15 ≡⟨⟩ 13 + 6 + 15 ≡⟨⟩ 19 + 15 ≡⟨⟩ 34 ∎

col3 : ℕ; col3 = 13 + 8  + 12 + 1
col3-ok : col3 ≡ 34
col3-ok = begin col3 ≡⟨⟩ 13 + 8 + 12 + 1 ≡⟨⟩ 21 + 12 + 1 ≡⟨⟩ 33 + 1 ≡⟨⟩ 34 ∎

-- 对角线
diag1 : ℕ; diag1 = 16 + 11 + 6 + 1
diag1-ok : diag1 ≡ 34
diag1-ok = begin diag1 ≡⟨⟩ 16 + 11 + 6 + 1 ≡⟨⟩ 27 + 6 + 1 ≡⟨⟩ 33 + 1 ≡⟨⟩ 34 ∎

diag2 : ℕ; diag2 = 13 + 10 + 7 + 4
diag2-ok : diag2 ≡ 34
diag2-ok = begin diag2 ≡⟨⟩ 13 + 10 + 7 + 4 ≡⟨⟩ 23 + 7 + 4 ≡⟨⟩ 30 + 4 ≡⟨⟩ 34 ∎
