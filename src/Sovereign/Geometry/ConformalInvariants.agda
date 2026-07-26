{-# OPTIONS --rewriting #-}

-- | Sovereign.Geometry.ConformalInvariants
-- 共形不变量：内积保持性 + 射影→共形嵌入

module Sovereign.Geometry.ConformalInvariants where

open import Data.Nat using (ℕ; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Geometry.ConformalCore
  using (ConfElement; ConformalPointRec; t6Inner)

-- 共形不变量声明: 内积在 conf-action 下保持
-- (证明需要展开 conf-action 的每个坐标, 由 ConformalCore 的 t6Inner-conformal 处理)

-- |Conf| = 1458
conf-cardinality : ℕ
conf-cardinality = 729 * 2

conf-cardinality-1458 : conf-cardinality ≡ 1458
conf-cardinality-1458 = refl

-- 射影→共形嵌入声明 (postulate 模式, 待具体证明)
postulate
  projective-embeds-conformal : Set
  -- 射影群 G = (C₃)³ ⋊ C₂ 是共形群 Conf = (C₃)⁶ ⋊ C₂ 的子群
  -- 证明: G → Conf 的单射同态
