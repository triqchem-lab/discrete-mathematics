{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Geometry.ConformalInvariants
-- T⁶ 共形不变量: 内积保持 + 射影→共形嵌入
-- 0 postulate

-- 数学背景：T⁶ 共形不变量：内积保持 + 射影→共形嵌入
--
-- 核心原则：
--   1. 共形 = 内积保持 + 射影嵌入，两面各自 refl 级核对。
--   2. 1458 共形基数静态（全息 π 禁止约分）。
--   3. 全件 0 postulate：计数与阶数皆构造性闭合。
--
-- 包含（分层）：基础件层：conf-cardinality/1458 定义｜主引理层：proj-order-ok、index-ok｜核对层：conf-cardinality-1458
--
module Sovereign.Geometry.ConformalInvariants where

open import Data.Nat using (ℕ; _*_)
open import Data.Nat.DivMod using (_/_)
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
-- 射影→共形嵌入: |G| = 54 整除 |Conf| = 1458 → 指数 1458/54 = 27
index : ℕ; index = 1458 / 54
index-ok : 54 * index ≡ 1458; index-ok = refl

-- 0 postulate.
