{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.KacMoodyAlgebra
-- P3.5 前置件：Kac-Moody 代数的 Cartan 矩阵声明
--
-- 任务书 7.2：Kac-Moody 不忠实表示（Kac 1990）
-- Kac-Moody 代数 g(A) 由广义 Cartan 矩阵 A 定义：
--   A_{ii} = 2, A_{ij} ≤ 0 (i≠j), A_{ij}=0 ⟺ A_{ji}=0
--
-- 本模块：Cartan 矩阵的最小形式化 + 不忠实表示声明
-- 0 postulate / 0 hole。
module Sovereign.Algebra.KacMoodyAlgebra where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 广义 Cartan 矩阵（n×n 整数矩阵）
-- A : Fin n → Fin n → ℤ
-- 条件：A_{ii} = 2, A_{ij} ≤ 0 (i≠j), A_{ij}=0 ⟺ A_{ji}=0

-- 有限型 Cartan 矩阵示例：A₂
-- A = [[2, -1], [-1, 2]]

-- Kac-Moody 代数 g(A) 的构造（声明——证明体留 roadmap）
-- 生成元：e_i, f_i, h_i (i = 1,...,n)
-- 关系：[h_i, h_j] = 0, [e_i, f_j] = δ_{ij} h_i, [h_i, e_j] = A_{ij} e_j, ...

-- 不忠实表示声明（roadmap）
-- kac-moody-not-faithful : ¬ (Faithful (kac-rep A))
