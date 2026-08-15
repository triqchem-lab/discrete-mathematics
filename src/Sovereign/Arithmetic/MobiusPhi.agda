{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Arithmetic.MobiusPhi
-- 11M 解析数论补强 — Möbius 函数与 Euler φ (12 的除数格上, 0 postulate)
--
-- 乘性数论的离散载体: 12 = 2²·3 的除数格 {1,2,3,4,6,12}
--   μ(1)=1, μ(2)=−1, μ(3)=−1, μ(4)=0, μ(6)=1, μ(12)=0
--   Möbius 反演: Σ_{d|12} μ(d) = 0 (n>1)
--   φ(12) = Σ_{d|12} μ(d)·(12/d) = 4 (与单位群 (Z/12Z)* ≅ V₄ 一致)
--   ζ 的 Euler 乘积注释 (乘性数论与有限域塔的桥)

module Sovereign.Arithmetic.MobiusPhi where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Möbius 值表 (12 的 6 个除数, ℤ)
mu-1 : ℤ ; mu-1 = + 1
mu-2 : ℤ ; mu-2 = -[1+ 0 ]
mu-3 : ℤ ; mu-3 = -[1+ 0 ]
mu-4 : ℤ ; mu-4 = + 0
mu-6 : ℤ ; mu-6 = + 1
mu-12 : ℤ ; mu-12 = + 0

-- Möbius 反演: Σ_{d|12} μ(d) = 0 (12 > 1)
mobius-sum : mu-1 + mu-2 + mu-3 + mu-4 + mu-6 + mu-12 ≡ + 0
mobius-sum = refl

-- φ(12) = Σ μ(d)·(12/d) = 4 — 与 (Z/12Z)* = {1,5,7,11} ≅ V₄ 一致
phi-12 : mu-1 * + 12 + mu-2 * + 6 + mu-3 * + 4 + mu-4 * + 3 + mu-6 * + 2 + mu-12 * + 1 ≡ + 4
phi-12 = refl

-- φ(12) 的单位群一致: |(Z/12Z)*| = 4 (Duodecial u1,u5,u7,u11)
-- 注释: Euler 乘积 (律算版) — 12 = 2²·3 → φ(12) = 12·(1−1/2)·(1−1/3) = 4,
--   整数化: φ = 2²⁻¹(2−1)·3⁰(3−1) = 2·2 = 4 — 与乘法群阶 |GF(9)*| = 8
--   的塔层关系见 FieldExtensionTower。

-- 0 postulate.
