{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BurauFaithful
-- P3.4：Burau 表示不忠实性声明
--
-- 任务书 7.1：Burau 表示的不忠实性（1991–1999）
--   Bigelow (1999) 证明 Burau 表示在 n≥5 时不忠实。
--   本模块声明形式化切入点，不包含完整证明（需辫群基础）。
--
-- 0 postulate / 0 hole。
-- 核心原则：
--   1. 本模块 = **声明层**（切入点 + 边界），不含证明体——C 级内容如实标注，不冒充 proven
--   2. 不忠实性结论归 Bigelow 1999（外部数学事实），本库只登记边界
-- 包含：BurauNotFaithful 切入点声明（类型级）+ 任务书 7.1 边界注记
module Sovereign.Algebra.GroupTheory.BurauFaithful where

open import Data.Nat using (ℕ)

-- Burau 表示：辫群 B_n → GL_{n-1}(Z[t,t^{-1}])
-- 忠实性：injective Burau
-- 不忠实性：¬ injective Burau（Bigelow 1999, n≥5）

-- 形式化切入点（类型级声明）
-- BurauNotFaithful : ∀ n → n ≥ 5 → ¬ (Injective (burau-rep n))
-- 需要：辫群 B_n 的形式化 + Burau 矩阵构造 + Bigelow 证明

-- 当前状态：无辫群基础（roadmap）
-- 前置件：A4Representations（表示论基础）、矩阵表示（GL_n）
