{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyNbrsNodup
--
-- **邻居表 `Nodup` 的前置 ③**：未被枚举的坐标不会被收进表里
--
-- ## 目标与关键教训
--
-- `T6CayleyDec` §9 的邻居表
-- ```
--   nbrsFrom x []       = []
--   nbrsFrom x (j ∷ js) = updAt j x ∷ updAt j (updAt j x) ∷ nbrsFrom x js
-- ```
--
-- ★ **不要**把陈述写成 `updAt j x ∉ nbrsFrom x js` —— 那样**索引被固定成具体项** ⇒
-- 匹配 `(here refl)` 会要求两个**不相等的具体项**定义性相等 ⇒ `UnificationStuck`。
-- 正解：**索引写成变量 `y`**，把「`y` 与两类项都不同」作为**前提**递下去：
-- ```
--   ★ nbrsFrom-not-in : (∀ j → j ∈ js → y ≢ updAt j x)
--                     → (∀ j → j ∈ js → y ≢ updAt j (updAt j x))
--                     → y ∉ nbrsFrom x js
-- ```
--
-- ## 核心原则
--   · 0 postulate / 0 hole

module Sovereign.Synthesis.Homotopy.T6CayleyNbrsNodup where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (Fin)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec; updAt)
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (nbrsFrom)

--------------------------------------------------------------------------------
-- §1. ★★ 主定理：表里的元素都「与已枚举坐标有关」
--
-- 归纳时 `(here refl)` 能成立，正因为索引是**变量** `y`（`refl` 只需绑定 `y`）。
--------------------------------------------------------------------------------

nbrsFrom-not-in : ∀ {n : ℕ} (x : T6Vec n) (js : List (Fin n)) (y : T6Vec n)
                → (∀ j → j ∈ js → y ≢ updAt j x)
                → (∀ j → j ∈ js → y ≢ updAt j (updAt j x))
                → y ∉ nbrsFrom x js
nbrsFrom-not-in x []       y h1 h2 = λ ()
nbrsFrom-not-in x (k ∷ ks) y h1 h2 (here eq) = h1 k (here refl) eq
nbrsFrom-not-in x (k ∷ ks) y h1 h2 (there (here eq)) = h2 k (here refl) eq
nbrsFrom-not-in x (k ∷ ks) y h1 h2 (there (there q)) =
  nbrsFrom-not-in x ks y
    (λ j m → h1 j (there m))
    (λ j m → h2 j (there m))
    q
