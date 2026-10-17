{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BraidGroup
-- P3.4 前置件：辫群 B_n 的最小形式化
--
-- 任务书 7.1：Burau 表示不忠实性（Bigelow 1999, n≥5）
-- 辫群 B_n 由 n-1 个生成元 σ₁,...,σ_{n-1} 满足：
--   ① σᵢσⱼ = σⱼσᵢ (|i-j| ≥ 2)
--   ② σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁
--
-- 本模块：B_3 的最小形式化（2 个生成元 + 关系声明）
-- ⚠ 2 个 postulate（关系声明，kind 待裁：见台账 BraidGroup 节点；诚实边界：非 0 postulate）
--
-- 核心原则：
--   1. 数学内容优先（背景→定义→引理→定理），证明每步可读；
--   2. 具名引理 + ∙/trans 链默认 ≤3 层；零洞零 postulate 目标；
--   3. 六段式分层：①头 ②导入 ③基础件 ④主引理 ⑤组合层 ⑥核对层。
--
-- 包含：record、module

module Sovereign.Algebra.GroupTheory.BraidGroup where

open import Relation.Binary.PropositionalEquality using (_≡_)

-- B₃ = ⟨σ₁, σ₂ | σ₁σ₂σ₁ = σ₂σ₁σ₂⟩ 的**展示定义**
-- 数学背景：presentation 的关系**只有辫关系一条**（自由群上单关系）；逆元是群结构的
--   导出（σ₁⁻¹ = inv σ₁，σ₁·σ₁⁻¹ = e 由逆公理给出）——不是独立生成元、不是关系。
--   （2026-10-11 核实 2 修正：此前 σᵢ-inv 作关系 = 额外公理，与 B₃ 定义不符，已改导出定理。）
-- 结构分层：群结构字段（定义"群"，同 UniversalAlgebra.Group 口径）+ 生成元 σ₁/σ₂ + 唯一关系。
-- ──────────────────────────────────────────────
-- ③ 基础件层 / ④ 主引理层（具名引理，∙ 链 ≤3）
-- ──────────────────────────────────────────────
record B3 : Set₁ where
  field
    carrier : Set
    e       : carrier
    _·_     : carrier → carrier → carrier
    inv     : carrier → carrier
    σ₁ σ₂   : carrier
    -- 群结构（结构定义，非 presentation 关系）
    assoc     : ∀ x y z → (x · y) · z ≡ x · (y · z)
    identityˡ : ∀ x → e · x ≡ x
    identityʳ : ∀ x → x · e ≡ x
    inverseʳ  : ∀ x → x · inv x ≡ e
    -- 唯一 presentation 关系
    braid-rel : (σ₁ · (σ₂ · σ₁)) ≡ (σ₂ · (σ₁ · σ₂))

-- 逆律 = 导出定理（投影逆公理，零新公理）
module _ (G : B3) where

-- ──────────────────────────────────────────────
-- ⑤ 组合层（主定理/装配收口）
-- ──────────────────────────────────────────────
  open B3 G
  σ₁-inv : σ₁ · inv σ₁ ≡ e
  σ₁-inv = inverseʳ σ₁
  σ₂-inv : σ₂ · inv σ₂ ≡ e
  σ₂-inv = inverseʳ σ₂

-- 诚实边界：B₃ 唯一性（泛性质：任意群 + 满足辫关系的两元素 → 唯一同态）与
--   Burau 表示实例留 roadmap。本模块交付：关系入定义的展示形态（3 postulate → 0）。
-- Burau 表示声明（roadmap）
-- burau-rep : B3 → GL₂(Z[t,t⁻¹])
-- burau-rep σ₁ = [[1-t, t], [1, 0]]
-- burau-rep σ₂ = [[1, 0], [t⁻¹, 1-t⁻¹]]
-- burau-faithful : ¬ (Injective burau-rep)  -- Bigelow 1999
