{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.KacMoodyFaithful
-- P3.5：Kac-Moody 代数不忠实表示声明
--
-- 任务书 7.2：Kac-Moody 代数的不忠实表示
--   Kac (1990) 研究 Kac-Moody 代数的表示论。
--   本模块声明形式化切入点，不包含完整证明（需李代数基础）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.KacMoodyFaithful where

open import Data.Nat using (ℕ)

-- Kac-Moody 代数：g(A) 由广义 Cartan 矩阵 A 定义
-- 不忠实表示：存在非忠实的 g(A) 模
-- 忠实性判据：Kac 的 Weyl 特征标公式

-- 形式化切入点（类型级声明）
-- KacMoodyNotFaithful : ∀ A → ¬ (Faithful (kac-rep A))
-- 需要：广义 Cartan 矩阵 + Kac-Moody 代数构造 + Weyl 特征标公式

-- 当前状态：无李代数基础（roadmap）
-- 前置件：jac_LieGroup（李代数括号）、A4Representations（表示论基础）
