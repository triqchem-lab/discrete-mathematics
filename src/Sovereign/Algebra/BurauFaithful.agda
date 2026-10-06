{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.BurauFaithful
-- P3.4：Burau 表示不忠实性声明
--
-- 任务书 7.1：Burau 表示的不忠实性（1991–1999）
--   Bigelow (1999) 证明 Burau 表示在 n≥5 时不忠实。
--   本模块声明形式化切入点，不包含完整证明（需辫群基础）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.BurauFaithful where

open import Data.Nat using (ℕ)

-- Burau 表示：辫群 B_n → GL_{n-1}(Z[t,t^{-1}])
-- 忠实性：injective Burau
-- 不忠实性：¬ injective Burau（Bigelow 1999, n≥5）

-- 形式化切入点（类型级声明）
-- BurauNotFaithful : ∀ n → n ≥ 5 → ¬ (Injective (burau-rep n))
-- 需要：辫群 B_n 的形式化 + Burau 矩阵构造 + Bigelow 证明

-- 当前状态：无辫群基础（roadmap）
-- 前置件：A4Representations（表示论基础）、矩阵表示（GL_n）
