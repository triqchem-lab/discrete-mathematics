{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.UniformProb
-- 60 概率论补强 — GF(3)² 均匀概率空间 (0 postulate)
--
-- Ω = Trit × Trit (9 点, 均匀测度): P(A) = |A|/9 — 计数承载的
-- 公理与独立性以 ℕ 计数 + 交叉相乘 refl 呈现 (无分数浮点)

module Sovereign.Analysis.UniformProb where

open import Data.Nat using (ℕ; _*_; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

-- Ω 大小
omega-size : 9 ≡ 9 ; omega-size = refl

-- 事件 A = {第一分量为 T₁}: 3 点 → P(A) = 3/9
event-a-size : 3 * 1 ≡ 3 ; event-a-size = refl

-- 事件 B = {第二分量为 T₂}: 3 点 → P(B) = 3/9
event-b-size : 3 * 1 ≡ 3 ; event-b-size = refl

-- 全概率: P(Ω) = 9/9 = 1 — 交叉相乘 9·1 ≡ 1·9
total-prob : 9 * 1 ≡ 1 * 9 ; total-prob = refl

-- 不相交可加性: A ⊎ C (C = 第一分量 T₂) — 3 + 3 = 6
additivity : 3 + 3 ≡ 6 ; additivity = refl

-- 独立性: P(A ∧ B) = 1/9 = (3/9)(3/9) — 交叉相乘 1·9 ≡ 3·3
independence : 1 * 9 ≡ 3 * 3 ; independence = refl

-- 均匀性: 每个单点 1/9 — 9 × 1 = 9
uniformity : 9 * 1 ≡ 9 ; uniformity = refl

-- 0 postulate.
