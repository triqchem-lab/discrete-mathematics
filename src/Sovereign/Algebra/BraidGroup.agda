{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.BraidGroup
-- P3.4 前置件：辫群 B_n 的最小形式化
--
-- 任务书 7.1：Burau 表示不忠实性（Bigelow 1999, n≥5）
-- 辫群 B_n 由 n-1 个生成元 σ₁,...,σ_{n-1} 满足：
--   ① σᵢσⱼ = σⱼσᵢ (|i-j| ≥ 2)
--   ② σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁
--
-- 本模块：B_3 的最小形式化（2 个生成元 + 关系声明）
-- ⚠ 2 个 postulate（关系声明，kind 待裁：见台账 BraidGroup 节点；诚实边界：非 0 postulate）
module Sovereign.Algebra.BraidGroup where

open import Relation.Binary.PropositionalEquality using (_≡_)

-- B₃ = ⟨σ₁, σ₂ | σ₁σ₂σ₁ = σ₂σ₁σ₂, σᵢσᵢ⁻¹ = e⟩ 的**展示定义**
-- 数学背景：关系是 B₃ 定义的组成部分（presentation），不是外来公理——
--   故关系以 record 字段承载（展示群八要素：载体 + 生成元 + 关系），零 postulate。
--   任何「B₃ 的模型」都是本 record 的一个实例；取用关系 = 投影字段。
record B3 : Set₁ where
  field
    Carrier : Set
    e      : Carrier
    σ₁ σ₂ σ₁⁻¹ σ₂⁻¹ : Carrier
    _·_    : Carrier → Carrier → Carrier
    -- ① 辫关系（定义性）
    braid-rel : (σ₁ · (σ₂ · σ₁)) ≡ (σ₂ · (σ₁ · σ₂))
    -- ② 逆元关系（定义性）
    σ₁-inv : (σ₁ · σ₁⁻¹) ≡ e
    σ₂-inv : (σ₂ · σ₂⁻¹) ≡ e

-- 诚实边界：群公理（结合律/单位律/左逆）与 B₃ 唯一性（泛性质）留 roadmap——
--   本模块交付的是「关系入定义」的展示形态（2 postulate → 0）。
-- Burau 表示声明（roadmap）
-- burau-rep : B3 → GL₂(Z[t,t⁻¹])
-- burau-rep σ₁ = [[1-t, t], [1, 0]]
-- burau-rep σ₂ = [[1, 0], [t⁻¹, 1-t⁻¹]]
-- burau-faithful : ¬ (Injective burau-rep)  -- Bigelow 1999
