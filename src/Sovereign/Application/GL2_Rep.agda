{-# OPTIONS --rewriting --guardedness #-}

-- | GL2_Rep —（勘误：旧头注 GL2_Rep，名≠模块名，已正名）— GL₂(GF(9)) 表示论: Burnside + 共轭类
-- 0 postulate

-- 核心原则：
--   1. GL₂(GF(9)) 阶数与中心的显式计算（q=9 代入，与 GL2TestVectors 穷举交叉互证）；
--   2. 诚实边界：本件是 GL₂(GF(9)) 群论面实例，非 Langlands 纲领对应。
-- 包含：order、center
module Sovereign.Application.GL2_Rep where

open import Data.Nat using (ℕ; _*_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- §1. GL₂(GF(9)) 基本数据 -----------------------------------------
-- |GL₂| = (9²-1)(9²-9) = 80·72 = 5760
-- 中心: Z ≅ GF(9)ˣ, |Z| = 8
-- 共轭类: 由有理标准形和 Jordan 块分类

-- 声明层升级（2026-10-11）：裸常数 → 公式定义 + 核对件
order-formula : ℕ; order-formula = (9 * 9 ∸ 1) * (9 * 9 ∸ 9)   -- (q²-1)(q²-9), q=9
order : ℕ; order = 5760
order-check : order-formula ≡ order; order-check = refl
center-formula : ℕ; center-formula = 9 ∸ 1                      -- |GF(9)ˣ| = q-1
center : ℕ; center = 8
center-check : center-formula ≡ center; center-check = refl

-- §2. Burnside Σdim² = |G| -----------------------------------------
-- 对任何有限群, Σdim(ρ)² = |G|.
-- A₄ (12) 实证: 3²+1²+1²+1² = 12 ✓ (A4Representations)
-- GL₂(5760) 的不可约表示由 Deligne-Lusztig 理论构造.

-- §3. 与 A₄ 的函子性 -----------------------------------------------
-- A₄ ⊂ GL₂(GF(9)): 限制映射 Res: Irr(GL₂) → Irr(A₄)
-- 分支律: 每个 GL₂ 不可约表示分解为 A₄ 不可约表示的和.
-- 本模块提供群阶和结构定义; 完整特征标表需 ~1000 行.
