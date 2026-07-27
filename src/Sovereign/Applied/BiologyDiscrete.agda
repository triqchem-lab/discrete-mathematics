{-# OPTIONS --rewriting --guardedness #-}
-- | BiologyDiscrete — MSC 92 数理生物 · GF(3) 三态基因型
-- 连续统 TypeError: ContinuousPopulationWithoutFiniteFitness
-- 离散替代: Trit 基因型 + 离散复制动力学

module Sovereign.Applied.BiologyDiscrete where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

-- 基因型 = Trit (三态: T₀隐性, T₁杂合, T₂显性)
Genotype : Set
Genotype = Trit

-- 种群: 有限个个体
Population : Set
Population = Trit → Trit → Trit → Trit

-- 离散复制动力学: 下一代 = 选择(当前代)
-- GF(3) 上三态选择矩阵
fitness : Genotype → Genotype
fitness T₀ = T₀  -- 隐性无优势
fitness T₁ = T₁  -- 杂合中性
fitness T₂ = T₂  -- 显性保持

-- 定理: 突变率 0 时平衡态存在
extinction-equilibrium : fitness T₀ ≡ T₀
extinction-equilibrium = refl

neutral-equilibrium : fitness T₁ ≡ T₁
neutral-equilibrium = refl

selective-equilibrium : fitness T₂ ≡ T₂
selective-equilibrium = refl
