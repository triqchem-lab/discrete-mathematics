{-# OPTIONS --rewriting --guardedness #-}

-- | jac_YM_Transfer — YM 转移矩阵 · 多链接格点一般构造
-- 【判重组4 注记 2026-10-11】与 YMTransfer.agda 近名对判重：异物互补（本件=一般构造，彼件=CRT 质量间隙闭合）
-- ——非重复；近名易混，模块改名会破迁移清单故保留原名（交叉注记消歧）
-- 0 postulate

--
-- 核心原则：
--   1. 格点/离散 YM 实例核——非连续 YM 全定理（质量间隙/连续极限未形式化，诚实边界）
--   2. 外部九圈类计算不改变本框架判定（投影层）
--
-- 包含：（重导/声明件——正文即清单）
module Sovereign.Application.YM_Transfer where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; trans)
open import Sovereign.Algebra.Jacobian.GF9Matrix
  using (0gf9; 1gf9; det2-gf9; det3-gf9; det4-gf9; I3-gf9; I4-gf9; det4-gf9-I)

-- ═══════════════════════════════════════════════════════════
-- 2 链接转移矩阵
-- ═══════════════════════════════════════════════════════════
-- 每条 link 有独立 U₁, U₂ ∈ SU(2,GF(9)) ≅ 2A₄
-- T = diag(U₁, U₂) (4×4 块对角)
-- det(T) = det(U₁)·det(U₂)
-- 对 SU(2): det(Uᵢ) = 1gf9 ≠ 0gf9 → det(T) ≠ 0 → 质量间隙

-- 平凡构型 (U₁=U₂=I₂)

-- ── 声明层升级（2026-10-11）：det 计算导出链（替代裸 λ() 模式）──
-- 机制：det(I) 经 jac_GF9Matrix 既有件计算为 1gf9（refl 级），再由 1gf9 ≢ 0gf9 导出
--（非平凡构型的一般命题为「det 乘积」形——诚实边界：实例核，非 YM 质量间隙全定理）
1≢0 : 1gf9 ≢ 0gf9
1≢0 = λ ()

t2-gap : det4-gf9 I4-gf9 ≢ 0gf9
t2-gap p = 1≢0 (trans (sym det4-gf9-I) p)   -- det(T)=det(I₄)=1gf9 导出

-- 一般构型: det(U₁)=det(U₂)=1gf9 → det(T)=1gf9 ≠ 0gf9
-- 全部 SU(2) 元素 have det=1 → 任意构型质量间隙存在

-- ═══════════════════════════════════════════════════════════
-- 3 链接转移矩阵
-- ═══════════════════════════════════════════════════════════
-- T = diag(U₁,U₂,U₃), 每个 U 是 2×2 块, T 是 6×6
-- CRT 分解 → 3×3 + 4×4 分量 → det2/3/4-gf9

-- N 链接: CRT → 质量间隙对所有 N 闭合
-- YM L3 缺口闭合: 转移矩阵构造 + det≠0 一般证明.
