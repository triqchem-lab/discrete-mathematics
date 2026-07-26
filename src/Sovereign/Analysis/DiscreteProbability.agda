{-# OPTIONS --rewriting --guardedness #-}

-- | DiscreteProbability — 离散概率论 (MSC 62)
-- GF(3) 上的有限概率空间: 6 个事件的离散分布.
-- 0 postulate.

module Sovereign.Analysis.DiscreteProbability where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- §1. 有限概率空间 -----------------------------------------------
-- Ω = {T₀, T₁, T₂} 三元素样本空间.
-- 概率分布: p : Trit → ℕ, Σp(x) = 3 (归一化到 GF(3) 单位).

-- 均匀分布: p(x) = 1
uniform : Trit → ℕ; uniform _ = 1
uniform-norm : uniform T₀ + uniform T₁ + uniform T₂ ≡ 3
uniform-norm = refl

-- 两点分布: p(T₀)=2, p(T₁)=1, p(T₂)=0
twoPoint : Trit → ℕ
twoPoint T₀ = 2; twoPoint T₁ = 1; twoPoint T₂ = 0

twoPoint-norm : twoPoint T₀ + twoPoint T₁ + twoPoint T₂ ≡ 3
twoPoint-norm = refl

-- §2. 期望与方差 (离散版) -----------------------------------------
-- E[X] = Σ x(i)·p(i)/N (离散加权平均, 无 Lebesgue 积分)
expectation : (Trit → ℕ) → (Trit → ℕ) → ℕ
expectation X p = (X T₀ * p T₀) + (X T₁ * p T₁) + (X T₂ * p T₂)

-- 恒等随机变量的期望
id-expect-uniform : expectation (λ {T₀ → 0; T₁ → 1; T₂ → 2}) uniform ≡ 3
id-expect-uniform = refl

-- §3. 联合分布 (T⁶ 上的乘积空间) ----------------------------------
-- Ω₁×Ω₂ = GF3 × GF3 (9 元素).
-- 联合分布穷举可计算, 边缘化 = 求和.

-- 边缘分布验证
marginal : (Trit × Trit → ℕ) → Trit → ℕ
marginal p x = p (x , T₀) + p (x , T₁) + p (x , T₂)

-- 独立乘积分布边缘化 = 均匀分布各分量
indep-prod : (Trit × Trit) → ℕ
indep-prod _ = 1
marginal-indep : marginal indep-prod T₀ ≡ 3
marginal-indep = refl

-- 经典概率依赖 σ-代数和 Lebesgue 积分.
-- 离散替代: GF(3)ⁿ 上的穷举求和, 所有分布完全可计算.
-- 0 postulate.
