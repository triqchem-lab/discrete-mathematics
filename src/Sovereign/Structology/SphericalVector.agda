{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.Structology.SphericalVector
-- 球谐矢量桥对象：T⁶ 相位格点 × C₄ 相位纤维 × A₄ 矢量表示 V3 的统一命名锚点
--
-- 数学背景: 判据第③层（维数塌缩截断）审计
--   （memory/t6-phase-preservation-audit.md, 2026-09-24）发现球谐矢量的 3D+
--   相位信息分布式承载于五锚点（C₄ 纤维 / A4Irrep V3 / T⁶ 格点 / 格点版
--   π₁(T⁶)≅T⁶Lattice / 零冥族），缺一个「它们是同一个对象」的桥——本模块即该桥。
--
-- 核心原则:
--   1. 载体 = T⁶ 离散相位格点（空间域）× DuodecPoint（GF(3) 幅度 × C₄ 相位纤维）
--      —— 承载 3D+ 球谐矢量相位，不做维度约化（反对标量/1D/2D 塌缩）
--   2. 三条生成律: 相位 90°×4 = id（α⁴=a₀）、幅度 3 步 = id（⊕³=T₀）、
--      联合走钟 12 步闭合（复用 DC 本源时钟 mixedOp-12-cycle）
--   3. 变换律 = A₄ 三维矢量不可约表示 V3（球谐 l=1 矢量内容）
--   4. 投影层（C₂ 符号 / C₁₂ 指标 / 实数角）禁止回流本模块
--      （相位不可约性元公理: memory/crt-wave-physics-not-modular-arithmetic.md:77）
module Sovereign.Structology.SphericalVector where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (DuodecPoint; AlphaPower; a0; a1; a2; a3; mixedOp; mixedOp^12; mixedOp-12-cycle)
open import Sovereign.Structology.T6 using (T6Lattice)
open import Sovereign.Structology.A4Representations using (A4Irrep; V3; dim)

-- 载体: T⁶ 相位格点 × DC 状态（幅度 GF(3) × 相位 C₄）
record SphericalVector : Set where
  constructor sv
  field
    site  : T6Lattice
    state : DuodecPoint

open SphericalVector

-- 相位 90° 旋转（纯相位步: 幅度不动, 相位 ×α）
rot4 : SphericalVector → SphericalVector
rot4 v = sv (site v) (mixedOp (state v) (T₀ , a1))

-- 相位四步闭合: α⁴ = a₀（12 case 表核对 ✓ ≤27）
rot4-4 : ∀ v → rot4 (rot4 (rot4 (rot4 v))) ≡ v
rot4-4 (sv s (T₀ , a0)) = refl; rot4-4 (sv s (T₀ , a1)) = refl
rot4-4 (sv s (T₀ , a2)) = refl; rot4-4 (sv s (T₀ , a3)) = refl
rot4-4 (sv s (T₁ , a0)) = refl; rot4-4 (sv s (T₁ , a1)) = refl
rot4-4 (sv s (T₁ , a2)) = refl; rot4-4 (sv s (T₁ , a3)) = refl
rot4-4 (sv s (T₂ , a0)) = refl; rot4-4 (sv s (T₂ , a1)) = refl
rot4-4 (sv s (T₂ , a2)) = refl; rot4-4 (sv s (T₂ , a3)) = refl

-- 幅度损益步（纯幅度步: 相位不动, 幅度 ⊕T₁）
amp3 : SphericalVector → SphericalVector
amp3 v = sv (site v) (mixedOp (state v) (T₁ , a0))

-- 幅度三步闭合: ⊕³ = T₀（12 case 表核对 ✓ ≤27）
amp3-3 : ∀ v → amp3 (amp3 (amp3 v)) ≡ v
amp3-3 (sv s (T₀ , a0)) = refl; amp3-3 (sv s (T₀ , a1)) = refl
amp3-3 (sv s (T₀ , a2)) = refl; amp3-3 (sv s (T₀ , a3)) = refl
amp3-3 (sv s (T₁ , a0)) = refl; amp3-3 (sv s (T₁ , a1)) = refl
amp3-3 (sv s (T₁ , a2)) = refl; amp3-3 (sv s (T₁ , a3)) = refl
amp3-3 (sv s (T₂ , a0)) = refl; amp3-3 (sv s (T₂ , a1)) = refl
amp3-3 (sv s (T₂ , a2)) = refl; amp3-3 (sv s (T₂ , a3)) = refl

-- 相位步与幅度步交换（作用于纤维不同分量; 12 case 表核对 ✓）
rot4-amp3-comm : ∀ v → rot4 (amp3 v) ≡ amp3 (rot4 v)
rot4-amp3-comm (sv s (T₀ , a0)) = refl; rot4-amp3-comm (sv s (T₀ , a1)) = refl
rot4-amp3-comm (sv s (T₀ , a2)) = refl; rot4-amp3-comm (sv s (T₀ , a3)) = refl
rot4-amp3-comm (sv s (T₁ , a0)) = refl; rot4-amp3-comm (sv s (T₁ , a1)) = refl
rot4-amp3-comm (sv s (T₁ , a2)) = refl; rot4-amp3-comm (sv s (T₁ , a3)) = refl
rot4-amp3-comm (sv s (T₂ , a0)) = refl; rot4-amp3-comm (sv s (T₂ , a1)) = refl
rot4-amp3-comm (sv s (T₂ , a2)) = refl; rot4-amp3-comm (sv s (T₂ , a3)) = refl

-- 联合走钟（生成元 g = (T₁,a1) 右步; 本源时钟过程, 非静态阶数）
clock12 : SphericalVector → SphericalVector
clock12 v = sv (site v) (mixedOp (state v) (T₁ , a1))

-- 走钟 12 步闭合（复用 DC 本源时钟定律; site 分量不动）
clock12-cycle : ∀ v → mixedOp^12 (state v) ≡ state v
clock12-cycle v = mixedOp-12-cycle (state v)

-- 变换律: 球谐矢量的矢量内容按 A₄ 三维矢量不可约表示 V3 变换（球谐 l=1）
spherical-vector-irrep : A4Irrep
spherical-vector-irrep = V3

spherical-vector-dim : dim spherical-vector-irrep ≡ 3
spherical-vector-dim = refl
