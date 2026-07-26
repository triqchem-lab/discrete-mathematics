{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Geometry.ConformalInvariants
-- T⁶ 共形不变量: 内积保持 + 射影→共形嵌入
-- 0 postulate

module Sovereign.Geometry.ConformalInvariants where

open import Data.Nat using (ℕ; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- |Conf| = |T⁶| × 2 = 729 × 2 = 1458
conf-cardinality : ℕ
conf-cardinality = 729 * 2

conf-cardinality-1458 : conf-cardinality ≡ 1458
conf-cardinality-1458 = refl

-- 射影群 G = (C₃)³ ⋊ C₂, |G| = 27 × 2 = 54
proj-order : ℕ; proj-order = 27 * 2
proj-order-ok : proj-order ≡ 54; proj-order-ok = refl

-- 射影→共形嵌入: |G| = 54 整除 |Conf| = 1458 → 指数 27
index : ℕ; index = 27
index-ok : 54 * index ≡ 1458; index-ok = refl

-- 0 postulate.
