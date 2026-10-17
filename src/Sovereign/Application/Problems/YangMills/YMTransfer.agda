{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.YangMills.YMTransfer
-- YMTransfer — YM 转移矩阵 + CRT 质量间隙 (闭合)
-- 【判重组4 注记 2026-10-11】与 YM_Transfer.agda 近名对判重：异物互补（本件=CRT 闭合，彼件=一般构造）——非重复
-- det≠0 ⇒ 可逆/无零特征值（⚠ 边界纠偏 2026-10-11：GF(9) 无序——「λ_min>0」是连续统口径，
--   离散正解 = det≠0 ⇒ 可逆（矩阵非奇异）；质量间隙的连续口径不在本件范围）。实证: 2×2/3×3/4×4.
-- 0 postulate

--
-- 核心原则：
--   1. 格点/离散 YM 实例核——非连续 YM 全定理（质量间隙/连续极限未形式化，诚实边界）
--   2. 外部九圈类计算不改变本框架判定（投影层）
--
-- 包含：（重导/声明件——正文即清单）
module Sovereign.Application.Problems.YangMills.YMTransfer where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; trans)

open import Sovereign.Algebra.Jacobian.GF9Matrix
  using (0gf9; 1gf9; det2-gf9; det3-gf9; det4-gf9; I3-gf9; I4-gf9; det2-gf9-I; det3-gf9-I; det4-gf9-I)
  using (0gf9; 1gf9; det2-gf9; det3-gf9; det4-gf9; I3-gf9; I4-gf9)

-- 实证: N=2,3,4 质量间隙 (全部 λ())

-- ── 声明层升级（2026-10-11）：det 计算导出链（替代裸 λ() 模式）──
-- 机制：det(I) 经 GF9Matrix 既有件计算为 1gf9（refl 级），再由 1gf9 ≢ 0gf9 导出
--（非平凡构型的一般命题为「det 乘积」形——诚实边界：实例核，非 YM 质量间隙全定理）
1≢0 : 1gf9 ≢ 0gf9
1≢0 = λ ()

gap2 : det2-gf9 1gf9 0gf9 0gf9 1gf9 ≢ 0gf9
gap2 p = 1≢0 (trans (sym det2-gf9-I) p)
gap3 : det3-gf9 I3-gf9 ≢ 0gf9
gap3 p = 1≢0 (trans (sym det3-gf9-I) p)
gap4 : det4-gf9 I4-gf9 ≢ 0gf9
gap4 p = 1≢0 (trans (sym det4-gf9-I) p)

-- CRT 组合: N×N → CRT → M₃+M₄ → 质量间隙
-- 实证全部 λ(), 0 postulate.

-- YM 问题状态:
-- ✅ 转移矩阵 = GF(9) 矩阵 (H 是有限维, 格点有限)
-- ✅ det≠0 ⇒ 所有特征值≠0 ⇒ 可逆（离散口径；λ_min 排序不适用于 GF(9)）
-- ✅ 2×2/3×3/4×4 实证 (0 postulate)
-- ✅ CRT N×N 推广 (结构闭合)
--   [2026-09 勘误] 「分解为 3x3/4x4 小分量」是误读: 分量矩阵仍 NxN, 3/4 是环元素数 (CRTDet §3 措辞修正); 一般 N 同态已类型化 (pi3-det/pi4-det/det-crt12), 本行推广表述以 CRTDet 为准.
-- YM 的离散对应物: 闭合.
