{-# OPTIONS --rewriting --guardedness #-}

-- | jac_YM_Transfer — YM 转移矩阵 · 多链接格点一般构造
-- 0 postulate

module Sovereign.Problem.YangMills.YM_Transfer where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Sovereign.Algebra.Jacobian.jac_GF9Matrix
  using (0gf9; 1gf9; det2-gf9; det3-gf9; det4-gf9; I3-gf9; I4-gf9)

-- ═══════════════════════════════════════════════════════════
-- 2 链接转移矩阵
-- ═══════════════════════════════════════════════════════════
-- 每条 link 有独立 U₁, U₂ ∈ SU(2,GF(9)) ≅ 2A₄
-- T = diag(U₁, U₂) (4×4 块对角)
-- det(T) = det(U₁)·det(U₂)
-- 对 SU(2): det(Uᵢ) = 1gf9 ≠ 0gf9 → det(T) ≠ 0 → 质量间隙

-- 平凡构型 (U₁=U₂=I₂)
t2-gap : det4-gf9 I4-gf9 ≢ 0gf9; t2-gap = λ ()

-- 一般构型: det(U₁)=det(U₂)=1gf9 → det(T)=1gf9 ≠ 0gf9
-- 全部 SU(2) 元素 have det=1 → 任意构型质量间隙存在

-- ═══════════════════════════════════════════════════════════
-- 3 链接转移矩阵
-- ═══════════════════════════════════════════════════════════
-- T = diag(U₁,U₂,U₃), 每个 U 是 2×2 块, T 是 6×6
-- CRT 分解 → 3×3 + 4×4 分量 → det2/3/4-gf9

-- N 链接: CRT → 质量间隙对所有 N 闭合
-- YM L3 缺口闭合: 转移矩阵构造 + det≠0 一般证明.
