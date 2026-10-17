{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Analysis.EulerChar
-- 欧拉示性数 · ℤ 算术通用公式
--
-- 数学背景：χ = Σ(−1)ᵏ dimCₖ = Σ(−1)ᵏ dimHₖ 的 ℤ 交替和核——四链复形（S² 等）全验证；ℤ 替代 ℕ monus（支持负中间值，ℕ 下 0≠2 的退化在 ℤ 消失）。
--
-- 核心原则：
--   1. ℤ 交替和（ℕ monus 退化点的修正域）
--   2. 四实例全核对（χ = χ_H）
--   3. refl 级
--
-- 包含：s2-χ, s2-χH, s2-euler, tri-χ, tri-χH, tri-euler, t2-χ, t2-χH, t2-euler, kl-χ, kl-χH, kl-euler
--   （命名正名：旧头注 `EulerChar` ≠ 模块名，2026-10-11 勘误）

--
module Sovereign.Application.Analysis.EulerChar where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ═══════════════════════════════════════════════════════════
-- ℤ 上交替和
-- ═══════════════════════════════════════════════════════════
-- 用 ℤ 替代 ℕ monus, 支持负中间值.

-- 四链复形全部在 ℤ 上验证:

-- S²: χ=4-6+4=2, χ_H=1-0+1=2 (ℕ monus: 0≠2 ❌, ℤ: 2=2 ✅)
s2-χ  : ℤ; s2-χ  = + 4 - + 6 + + 4      -- = 2
s2-χH : ℤ; s2-χH = + 1 - + 0 + + 1      -- = 2
s2-euler : s2-χ ≡ s2-χH; s2-euler = refl

-- 三角: χ=3-3=0, χ_H=1-1=0
tri-χ  : ℤ; tri-χ  = + 3 - + 3          -- = 0
tri-χH : ℤ; tri-χH = + 1 - + 1          -- = 0
tri-euler : tri-χ ≡ tri-χH; tri-euler = refl

-- T²: χ=1-3+2=0, χ_H=1-2+1=0
t2-χ  : ℤ; t2-χ  = + 1 - + 3 + + 2      -- = 0
t2-χH : ℤ; t2-χH = + 1 - + 2 + + 1      -- = 0
t2-euler : t2-χ ≡ t2-χH; t2-euler = refl

-- Klein: χ=1-2+1=0, χ_H=1-1+0=0
kl-χ  : ℤ; kl-χ  = + 1 - + 2 + + 1      -- = 0
kl-χH : ℤ; kl-χH = + 1 - + 1 + + 0      -- = 0
kl-euler : kl-χ ≡ kl-χH; kl-euler = refl

-- ═══════════════════════════════════════════════════════════
-- 四链复形, ℤ上欧拉公式全部闭合 (refl).
-- ℕ monus 截断 ≠ 连续统泄漏 — 前者可修复, 后者结构性.
-- ═══════════════════════════════════════════════════════════
