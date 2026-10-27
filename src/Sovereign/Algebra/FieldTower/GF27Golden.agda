{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.FieldTower.GF27Golden —— GF(27) golden 表**校验编码**（pin）
--
-- ⚠ **校验编码，不是数学证明**：本文件由 `scripts/gen-gf27-golden.py` 生成
--   （不要手改），把 `GF27.agda` 的 toGF27 / fromGF27 两张表钉成字面量，
--   供跨仓对拍（trha: `test/golden/gf27.json` ← 同一脚本写出）。
--   `pin-to` / `pin-from` 的 refl 只证明「golden 没有抄错表」，
--   **不承载任何数学结论**（依 2026-10-26 裁定：数值等式不作证明，
--   除非给结构理由；此处显然没有，故只当 pin）。
--
--   若 `GF27.agda` 的表发生变化 ⇒ 本文件 refl 必红 ⇒ 重新跑生成器同步 golden。

module Sovereign.Algebra.FieldTower.GF27Golden where

open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; _∷_; []; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.FieldTower.GF27
  using ( GF27; GF27Star; toGF27; fromGF27
        ; pow0; pow1; pow2; pow3; pow4; pow5; pow6
        ; pow7; pow8; pow9; pow10; pow11; pow12; pow13
        ; pow14; pow15; pow16; pow17; pow18; pow19; pow20
        ; pow21; pow22; pow23; pow24; pow25
        )

Coord = GF27

-- toGF27 pow0..pow25 的 26 组坐标（与 golden/gf27.json 的 star[].coords 逐项同源）
goldenTo : Vec Coord 26
goldenTo = (T₁ , T₀ , T₀) ∷ (T₀ , T₁ , T₀) ∷ (T₀ , T₀ , T₁) ∷ (T₂ , T₁ , T₀) ∷ (T₀ , T₂ , T₁) ∷ (T₂ , T₁ , T₂) ∷ (T₁ , T₁ , T₁) ∷ (T₂ , T₂ , T₁) ∷ (T₂ , T₀ , T₂) ∷ (T₁ , T₁ , T₀) ∷ (T₀ , T₁ , T₁) ∷ (T₂ , T₁ , T₁) ∷ (T₂ , T₀ , T₁) ∷ (T₂ , T₀ , T₀) ∷ (T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₂) ∷ (T₁ , T₂ , T₀) ∷ (T₀ , T₁ , T₂) ∷ (T₁ , T₂ , T₁) ∷ (T₂ , T₂ , T₂) ∷ (T₁ , T₁ , T₂) ∷ (T₁ , T₀ , T₁) ∷ (T₂ , T₂ , T₀) ∷ (T₀ , T₂ , T₂) ∷ (T₁ , T₂ , T₂) ∷ (T₁ , T₀ , T₂) ∷ []

pin-to : map toGF27 (pow0 ∷ pow1 ∷ pow2 ∷ pow3 ∷ pow4 ∷ pow5 ∷ pow6 ∷ pow7 ∷ pow8 ∷ pow9 ∷ pow10 ∷ pow11 ∷ pow12 ∷ pow13 ∷ pow14 ∷ pow15 ∷ pow16 ∷ pow17 ∷ pow18 ∷ pow19 ∷ pow20 ∷ pow21 ∷ pow22 ∷ pow23 ∷ pow24 ∷ pow25 ∷ []) ≡ goldenTo
pin-to = refl

-- fromGF27 的 27 个子句按原顺序（第 1 条是零元折到 pow0 的约定）
goldenFrom : Vec GF27Star 27
goldenFrom = pow0 ∷ pow0 ∷ pow13 ∷ pow1 ∷ pow14 ∷ pow2 ∷ pow15 ∷ pow9 ∷ pow16 ∷ pow3 ∷ pow22 ∷ pow21 ∷ pow25 ∷ pow12 ∷ pow8 ∷ pow10 ∷ pow17 ∷ pow4 ∷ pow23 ∷ pow6 ∷ pow20 ∷ pow18 ∷ pow24 ∷ pow11 ∷ pow5 ∷ pow7 ∷ pow19 ∷ []

allCoords : Vec Coord 27
allCoords = (T₀ , T₀ , T₀) ∷ (T₁ , T₀ , T₀) ∷ (T₂ , T₀ , T₀) ∷ (T₀ , T₁ , T₀) ∷ (T₀ , T₂ , T₀) ∷ (T₀ , T₀ , T₁) ∷ (T₀ , T₀ , T₂) ∷ (T₁ , T₁ , T₀) ∷ (T₁ , T₂ , T₀) ∷ (T₂ , T₁ , T₀) ∷ (T₂ , T₂ , T₀) ∷ (T₁ , T₀ , T₁) ∷ (T₁ , T₀ , T₂) ∷ (T₂ , T₀ , T₁) ∷ (T₂ , T₀ , T₂) ∷ (T₀ , T₁ , T₁) ∷ (T₀ , T₁ , T₂) ∷ (T₀ , T₂ , T₁) ∷ (T₀ , T₂ , T₂) ∷ (T₁ , T₁ , T₁) ∷ (T₁ , T₁ , T₂) ∷ (T₁ , T₂ , T₁) ∷ (T₁ , T₂ , T₂) ∷ (T₂ , T₁ , T₁) ∷ (T₂ , T₁ , T₂) ∷ (T₂ , T₂ , T₁) ∷ (T₂ , T₂ , T₂) ∷ []

pin-from : map fromGF27 allCoords ≡ goldenFrom
pin-from = refl
