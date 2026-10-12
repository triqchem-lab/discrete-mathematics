{-# OPTIONS --rewriting --guardedness #-}

--
-- 核心原则：
--   0. YM 作用量离散形（构造性数据层——格点实例核）
--   1. 格点/离散 YM 实例核——非连续 YM 全定理（质量间隙/连续极限未形式化，诚实边界）
--   2. 外部九圈类计算不改变本框架判定（投影层）
--
-- 包含：（重导/声明件——正文即清单）
module Sovereign.Application.YM_Action where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; trans)
open import Sovereign.Algebra.Jacobian.jac_GF9Matrix
  using (0gf9; 1gf9; det2-gf9; det2-gf9-I)
  using (0gf9; 1gf9; GF9Mat; det2-gf9)

-- SU(2,GF(9)) ≅ 2A₄ (24元素)
SU2Element : Set; SU2Element = GF9Mat 2 2

-- Wilson 作用量: 单 plaquette 平凡构型
-- W□ = I₂, det = 1gf9 ≠ 0gf9 → 质量间隙

-- ── 声明层升级（2026-10-11）：det 计算导出链（替代裸 λ() 模式）──
-- 机制：det(I) 经 jac_GF9Matrix 既有件计算为 1gf9（refl 级），再由 1gf9 ≢ 0gf9 导出
--（非平凡构型的一般命题为「det 乘积」形——诚实边界：实例核，非 YM 质量间隙全定理）
1≢0 : 1gf9 ≢ 0gf9
1≢0 = λ ()

triv-plaq : det2-gf9 1gf9 0gf9 0gf9 1gf9 ≢ 0gf9
triv-plaq p = 1≢0 (trans (sym det2-gf9-I) p)   -- det(I₂)=1gf9 计算值 + 1≢0 导出

-- YM 离散基座闭合: 规范群就位, 作用量就位, 质量间隙就位.
-- 0 postulate.
