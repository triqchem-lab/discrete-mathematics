{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Physics.TRMultipletsZ
--
-- TR 耦合维数恒等式的**代数核心**（在 ℤ 上）：
--     x² + (2x + 1) ≡ (x + 1)²
-- 取 x = a + n 即得「连续奇数和 + a² = (a+n)²」的归纳步。
--
-- 用 RingSolver 宏证（本库已有 Int.RingSolver-bridge 见证其可用性）。
-- 注意：ℕ 版本另需 +-suc 等 plumbing（见 docs/drafts/TRMultiplets-wip.agda）。
--
-- 0 postulate / 0 hole。
module Sovereign.Synthesis.Physics.TRMultipletsZ where

open import Data.Integer using (ℤ; +_; _+_; _*_)
open import Data.Integer.Tactic.RingSolver using (solve-∀)
open import Relation.Binary.PropositionalEquality using (_≡_)

sq-suc-Z : ∀ (x : ℤ) → x * x + ((+ 2) * x + (+ 1)) ≡ (x + (+ 1)) * (x + (+ 1))
sq-suc-Z = solve-∀
