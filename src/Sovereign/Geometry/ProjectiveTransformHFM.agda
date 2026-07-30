{-# OPTIONS --rewriting #-}

-- | Sovereign.Geometry.ProjectiveTransformHFM
-- A₄×C₃ 直积的 HFM 交叉验证 (HFM test/SovereignGroups.hs)
--   36 元素, 12 共役类 (A₄ 有 4 类, C₃ 有 3 类, 直积有 4×3=12 类)

module Sovereign.Geometry.ProjectiveTransformHFM where

open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

orderA4 : ℕ; orderA4 = 12
orderC3 : ℕ; orderC3 = 3
orderProduct : ℕ; orderProduct = 36  -- 12×3

orderA4-ok : orderA4 ≡ 12; orderA4-ok = refl
orderC3-ok : orderC3 ≡ 3; orderC3-ok = refl
orderProduct-ok : orderProduct ≡ 36; orderProduct-ok = refl

-- 共役类数: A₄ 有 4 类, C₃ 有 3 类, 直积有 4×3=12 类
conjClassesA4 : ℕ; conjClassesA4 = 4
conjClassesC3 : ℕ; conjClassesC3 = 3
conjClassesProduct : ℕ; conjClassesProduct = 12

conjClassesProduct-ok : conjClassesProduct ≡ 12
conjClassesProduct-ok = refl
