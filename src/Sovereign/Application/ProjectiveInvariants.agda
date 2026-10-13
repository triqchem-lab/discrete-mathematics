{-# OPTIONS --rewriting #-}

-- | Sovereign.Application.ProjectiveInvariants
-- 射影不变量 —— 4320D 轨道的 144 × 46 分解与整除刚性。
--
-- 数学背景：射影轨道规模 6624 = 144 × 46（SOVEREIGN_LCM 的极分解：144 = POLAR，46 = TORUS）。
--   不变量：6624 % 46 ≡ 0 与 6624 % 144 ≡ 0（两因子均整除，refl 级验证），
--   即极分解的两个分量都是射影轨道规模的刚性因子（π 禁止约分）。
module Sovereign.Application.ProjectiveInvariants where

open import Data.Nat using (ℕ; _+_; _*_; _%_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Synthesis.Winding
  using (PolarWinding; ToroidalWinding)
open import Sovereign.Synthesis.MagicSquare144
  using (FULL_TOUR)
open import Sovereign.Application.ProjectiveCore
  using (GElement; g-action-full)

-- 6624 = 144 × 46 (直接使用 refl 验证)
t : ℕ
t = 144 * 46

t-is-6624 : t ≡ 6624
t-is-6624 = refl

-- 对偶: (144 * 46) % 46 ≡ 0
p1 : (144 * 46) % 46 ≡ 0
p1 = refl

-- (144 * 46) % 144 ≡ 0
p2 : (144 * 46) % 144 ≡ 0
p2 = refl
