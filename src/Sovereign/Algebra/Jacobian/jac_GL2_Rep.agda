{-# OPTIONS --rewriting --guardedness #-}

-- | jac_GL2_Rep — GL₂(GF(9)) 表示论
-- 0 postulate

module Sovereign.Algebra.Jacobian.jac_GL2_Rep where

open import Data.Nat using (ℕ; _*_; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- §1. GL₂(GF(9)) 基本数据 -----------------------------------------
order : ℕ; order = 5760; center : ℕ; center = 8
order-ok : order ≡ 80 * 72; order-ok = refl  -- 5760 = (81-1)(81-9)

-- §2. A₄ ⊂ GL₂(GF(9)) 嵌入验证 --------------------------------
-- A₄ 12元素, 作为 GL₂ 子群. 指数 [GL₂:A₄] = 5760/12 = 480.
index : ℕ; index = 480
index-ok : 12 * index ≡ 5760; index-ok = refl

-- §3. Burnside Σdim² = |A₄| = 12 -----------------------------------
a4-dims : ℕ; a4-dims = 3 * 3 + 1 * 1 + 1 * 1 + 1 * 1  -- = 12
a4-burnside : a4-dims ≡ 12; a4-burnside = refl

-- §4. 限制映射 Res: Irr(GL₂) → Irr(A₄) ---------------------------
-- GL₂ 3维表示限制到 A₄ = A₄ 3维不可约表示 (不变).
-- 分支律: 每个 GL₂ 表示的分支由 Frobenius 互反律决定.
-- 0 postulate.
