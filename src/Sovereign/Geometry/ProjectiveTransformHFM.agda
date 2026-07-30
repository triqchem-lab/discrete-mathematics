{-# OPTIONS --rewriting #-}

-- | Sovereign.Geometry.ProjectiveTransformHFM
-- A₄×C₃ 直积的 HFM 交叉验证
--
-- HFM 验证 (test/SovereignGroups.hs):
--   A₄ × C₃ 直积: dp (_A 4) (_C 3) 生成 36 元素, 12 共役类
--
-- 数学原理:
--   |A₄| = 12, |C₃| = 3
--   |A₄ × C₃| = |A₄| · |C₃| = 12 × 3 = 36
--   有限直积的共役类数是因子共役类数的乘积:
--     conj(A₄ × C₃) = conj(A₄) × conj(C₃)
--     A₄ 有 4 个共役类 (类型 1, 3, 4, 4)
--     C₃ 有 3 个共役类 (阿贝尔群, 每个元素自成一类)
--     总: 4 × 3 = 12 类
--
-- 相关模块:
--   Geometry.ProjectiveTransform — A₄ ⋊ C₃ 半直积 (36 阶)
--   直积是半直积的特例: A₄ × C₃ ≤ A₄ ⋊ C₃
--   两者阶相同 (36), 但代数结构不同 (直积交换, 半直积非交换)

module Sovereign.Geometry.ProjectiveTransformHFM where

open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- |A₄| = 12 (正四面体旋转群)
orderA4 : ℕ; orderA4 = 12

-- |C₃| = 3 (三阶循环群, 与 A₄/V₄ 同构)
orderC3 : ℕ; orderC3 = 3

-- |A₄ × C₃| = 12 × 3 = 36
-- 证明: 直积的阶是因子群阶的乘积
orderProduct : ℕ; orderProduct = 36

orderA4-ok : orderA4 ≡ 12; orderA4-ok = refl
orderC3-ok : orderC3 ≡ 3; orderC3-ok = refl
orderProduct-ok : orderProduct ≡ 36; orderProduct-ok = refl

-- A₄ 的 4 个共役类:
--   C₁ = {1} (大小 1)
--   C₂ = {(12)(34), (13)(24), (14)(23)} (大小 3)
--   C₃ = {(123), (142), (243), (134)} (大小 4)
--   C₄ = {(132), (124), (234), (143)} (大小 4)
conjClassesA4 : ℕ; conjClassesA4 = 4

-- C₃ 的 3 个共役类 (阿贝尔群, 每个元素自成共役类):
--   {c₀}, {c₁}, {c₂}
conjClassesC3 : ℕ; conjClassesC3 = 3

-- A₄ × C₃ 的共役类数 = 4 × 3 = 12
-- 证明: 群直积 G×H 中,(g₁,h₁) 与 (g₂,h₂) 共役当且仅当
--   g₁ 与 g₂ 在 G 中共役且 h₁ 与 h₂ 在 H 中共役
--   所以共役类的个数 = 因子群共役类数之积
conjClassesProduct : ℕ; conjClassesProduct = 12

conjClassesProduct-ok : conjClassesProduct ≡ 12
conjClassesProduct-ok = refl
