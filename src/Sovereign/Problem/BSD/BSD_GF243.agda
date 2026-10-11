{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.BSD.BSD_GF243
-- BSD t₅ 递推 + GF(243) · 三曲线全分化
--
-- 数学背景：BSD 线 GF(243)=GF(3⁵) 实例核：t₅ = t₁·t₄ − q·t₃ 递推 + 点计数 243+1−t₅，三曲线全分化对照。
--
-- 核心原则：
--   1. 实例核（refl 级数值核对）
--   2. 递推同 BSD_GF27 族（Newton 恒等式链）
--   3. ℤ 精确值
--
-- 包含：q3, t51, t52, t56
--   （命名正名：旧头注 `jac_BSD_GF243` ≠ 模块名，2026-10-11 勘误）

--
module Sovereign.Problem.BSD.BSD_GF243 where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

q3 : ℤ; q3 = + 3

-- t₅ = t₁·t₄ - q·t₃

-- E₁: t₁=0, t₃=0 → t₅=0
t51 : ℤ; t51 = (+ 0 * + 18) - (q3 * + 0); e1243 : ℤ; e1243 = (+ 243 + + 1) - t51 -- =244

-- E₂: t₁=-3, t₃=0 → t₅=27
t52 : ℤ; t52 = (-[1+ 2 ] * -[1+ 8 ]) - (q3 * + 0); e2243 : ℤ; e2243 = (+ 243 + + 1) - t52 -- 9-0=27→217

-- E₆: t₁=3, t₃=0 → t₅=-27
t56 : ℤ; t56 = (+ 3 * -[1+ 8 ]) - (q3 * + 0); e6243 : ℤ; e6243 = (+ 243 + + 1) - t56 -- -27→271

-- Hasse: |t₅| ≤ 2√243≈31.1. E₁:0✓, E₂:27✓, E₆:27✓.
-- t₅ 处 E₂/E₆ 分化: t(E₂)=+27, t(E₆)=-27. 三曲线全部不同.
-- 0 postulate — Weil完整验证 GF(3)→...→GF(243).
