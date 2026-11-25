{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.GaugeArtifactF9
-- 规范伪影定理: F₉ 格点上「挠场」= 标架非协变余项的实体化（M10）
--
-- 数学背景（Deep Research §五 离散模型, 2026-11-25; oracle gauge 模式全枚举核对 ✓）:
--   4×4 周期格点（16 顶点），每顶点配置:
--   · 纯规范链变量 U = h·h(shift)⁻¹（h : 顶点 → C₈ 规范选取, oracle 冻结）——
--     其离散曲率**恒零**（绝对平行, 同 TeleparallelA4.plaquette-collapse 形态）;
--   · **固定标架** e = ((1,0), (0,1))（Shipov 式: 拒绝同步变换）——
--     离散嘉当挠率 T = e_x + U_x·e_y(x+1) − e_y − U_y·e_x(y+1) 在 14/16 顶点**非零**;
--   · **联合局域规范变换** e' = h·e（U 纯规范保持不变）——
--     同一挠率公式在全格点**恒零**（★ 主定理 tjnt-zero, 16 条 refl）。
--   ⟹ **「挠场」= 标架非协变余项的规范伪影**: Shipov 把纯规范联络的标架
--   非协变余项实体化为物理场（其本人承认 T_ijk 在 O(3,1) 下非张量变换）;
--   本件在 F₉ 格点上把该机制**完全枚举并形式化**（伪影出现/消失均可计算）。
--
-- 诚实边界:
--   · F₉ 格点上的**离散代数裁决**, 不是对连续物理的证伪;
--   · 全件表格 oracle emit 逐字冻结（先算后验）; 独立具名引理形态（坑#5/#6）。

module Sovereign.Application.Problems.RH.GaugeArtifactF9 where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Application.Problems.RH.CountF9All

--------------------------------------------------------------------------------
-- §1. 载体: F₉ 求负 + 挠率公式（共享算子; 两套标架用同一公式）
--------------------------------------------------------------------------------

f9neg : F9 → F9
f9neg (mkF9 a b) = mkF9 (negate a) (negate b)

torsionOf : F9 → F9 → F9 → F9 → F9 → F9 → F9
torsionOf ex ey ux uy exy eyx =
  f9add (f9add ex (f9mul ux eyx))
        (f9add (f9neg ey) (f9neg (f9mul uy exy)))

--------------------------------------------------------------------------------
-- §2. 格点与邻居
--------------------------------------------------------------------------------

data Vtx : Set where
  v00 v01 v02 v03 v10 v11 v12 v13 v20 v21 v22 v23 v30 v31 v32 v33 : Vtx

next-x next-y : Vtx → Vtx


next-x v00 = v10
next-x v01 = v11
next-x v02 = v12
next-x v03 = v13
next-x v10 = v20
next-x v11 = v21
next-x v12 = v22
next-x v13 = v23
next-x v20 = v30
next-x v21 = v31
next-x v22 = v32
next-x v23 = v33
next-x v30 = v00
next-x v31 = v01
next-x v32 = v02
next-x v33 = v03
next-y v00 = v01
next-y v01 = v02
next-y v02 = v03
next-y v03 = v00
next-y v10 = v11
next-y v11 = v12
next-y v12 = v13
next-y v13 = v10
next-y v20 = v21
next-y v21 = v22
next-y v22 = v23
next-y v23 = v20
next-y v30 = v31
next-y v31 = v32
next-y v32 = v33
next-y v33 = v30

zero9 : F9
zero9 = mkF9 T₀ T₀

-- §M1. h 场（规范选取; C₈ 元素; oracle emit 逐字）
hv : Vtx → F9
hv v00 = mkF9 T₂ T₁
hv v01 = mkF9 T₂ T₁
hv v02 = mkF9 T₂ T₁
hv v03 = mkF9 T₁ T₂
hv v10 = mkF9 T₀ T₂
hv v11 = mkF9 T₂ T₁
hv v12 = mkF9 T₀ T₂
hv v13 = mkF9 T₁ T₁
hv v20 = mkF9 T₂ T₁
hv v21 = mkF9 T₂ T₀
hv v22 = mkF9 T₀ T₂
hv v23 = mkF9 T₁ T₁
hv v30 = mkF9 T₁ T₀
hv v31 = mkF9 T₀ T₁
hv v32 = mkF9 T₂ T₁
hv v33 = mkF9 T₀ T₂

-- §M2. 链变量（纯规范 U = h·h(shift)⁻¹; oracle F9INV_TAB 冻结）
uxp : Vtx → F9
uxp v00 = mkF9 T₂ T₂
uxp v01 = mkF9 T₁ T₀
uxp v02 = mkF9 T₂ T₂
uxp v03 = mkF9 T₀ T₂
uxp v10 = mkF9 T₁ T₂
uxp v11 = mkF9 T₁ T₂
uxp v12 = mkF9 T₁ T₀
uxp v13 = mkF9 T₁ T₀
uxp v20 = mkF9 T₂ T₁
uxp v21 = mkF9 T₀ T₁
uxp v22 = mkF9 T₁ T₂
uxp v23 = mkF9 T₂ T₁
uxp v30 = mkF9 T₁ T₁
uxp v31 = mkF9 T₂ T₁
uxp v32 = mkF9 T₁ T₀
uxp v33 = mkF9 T₂ T₁

uyp : Vtx → F9
uyp v00 = mkF9 T₁ T₀
uyp v01 = mkF9 T₁ T₀
uyp v02 = mkF9 T₂ T₀
uyp v03 = mkF9 T₂ T₀
uyp v10 = mkF9 T₁ T₂
uyp v11 = mkF9 T₂ T₂
uyp v12 = mkF9 T₁ T₁
uyp v13 = mkF9 T₂ T₁
uyp v20 = mkF9 T₁ T₂
uyp v21 = mkF9 T₀ T₂
uyp v22 = mkF9 T₁ T₁
uyp v23 = mkF9 T₀ T₂
uyp v30 = mkF9 T₀ T₂
uyp v31 = mkF9 T₂ T₁
uyp v32 = mkF9 T₂ T₂
uyp v33 = mkF9 T₀ T₂

-- §3. 两套标架
efx efy : Vtx → F9
efx v = mkF9 T₁ T₀
efy v = mkF9 T₀ T₁

efx' efy' : Vtx → F9
efx' v = f9mul (hv v) (mkF9 T₁ T₀)
efy' v = f9mul (hv v) (mkF9 T₀ T₁)

-- §4. 两张挠率表
tfix : Vtx → F9
tfix v = torsionOf (efx v) (efy v) (uxp v) (uyp v) (efx (next-y v)) (efy (next-x v))

tjnt : Vtx → F9
tjnt v = torsionOf (efx' v) (efy' v) (uxp v) (uyp v) (efx' (next-y v)) (efy' (next-x v))

-- §5. ★ 主定理: 联合规范变换后挠率恒零
tjnt-zero : ∀ v → tjnt v ≡ zero9
tjnt-zero v00 = refl
tjnt-zero v01 = refl
tjnt-zero v02 = refl
tjnt-zero v03 = refl
tjnt-zero v10 = refl
tjnt-zero v11 = refl
tjnt-zero v12 = refl
tjnt-zero v13 = refl
tjnt-zero v20 = refl
tjnt-zero v21 = refl
tjnt-zero v22 = refl
tjnt-zero v23 = refl
tjnt-zero v30 = refl
tjnt-zero v31 = refl
tjnt-zero v32 = refl
tjnt-zero v33 = refl

-- §6. 伪影见证: 固定标架挠率逐点值
tfix-val-v00 : tfix v00 ≡ mkF9 T₁ T₁
tfix-val-v00 = refl
tfix-val-v01 : tfix v01 ≡ mkF9 T₀ T₀
tfix-val-v01 = refl
tfix-val-v02 : tfix v02 ≡ mkF9 T₀ T₁
tfix-val-v02 = refl
tfix-val-v03 : tfix v03 ≡ mkF9 T₀ T₂
tfix-val-v03 = refl
tfix-val-v10 : tfix v10 ≡ mkF9 T₁ T₁
tfix-val-v10 = refl
tfix-val-v11 : tfix v11 ≡ mkF9 T₀ T₁
tfix-val-v11 = refl
tfix-val-v12 : tfix v12 ≡ mkF9 T₀ T₂
tfix-val-v12 = refl
tfix-val-v13 : tfix v13 ≡ mkF9 T₂ T₂
tfix-val-v13 = refl
tfix-val-v20 : tfix v20 ≡ mkF9 T₂ T₂
tfix-val-v20 = refl
tfix-val-v21 : tfix v21 ≡ mkF9 T₀ T₀
tfix-val-v21 = refl
tfix-val-v22 : tfix v22 ≡ mkF9 T₁ T₂
tfix-val-v22 = refl
tfix-val-v23 : tfix v23 ≡ mkF9 T₀ T₂
tfix-val-v23 = refl
tfix-val-v30 : tfix v30 ≡ mkF9 T₀ T₁
tfix-val-v30 = refl
tfix-val-v31 : tfix v31 ≡ mkF9 T₁ T₀
tfix-val-v31 = refl
tfix-val-v32 : tfix v32 ≡ mkF9 T₂ T₁
tfix-val-v32 = refl
tfix-val-v33 : tfix v33 ≡ mkF9 T₀ T₂
tfix-val-v33 = refl

-- 伪影见证（14 个非零顶点 ≢ zero9; 构造子场不等, () 拦截）
tfix-ne-v00 : tfix v00 ≢ zero9
tfix-ne-v00 ()
tfix-ne-v02 : tfix v02 ≢ zero9
tfix-ne-v02 ()
tfix-ne-v03 : tfix v03 ≢ zero9
tfix-ne-v03 ()
tfix-ne-v10 : tfix v10 ≢ zero9
tfix-ne-v10 ()
tfix-ne-v11 : tfix v11 ≢ zero9
tfix-ne-v11 ()
tfix-ne-v12 : tfix v12 ≢ zero9
tfix-ne-v12 ()
tfix-ne-v13 : tfix v13 ≢ zero9
tfix-ne-v13 ()
tfix-ne-v20 : tfix v20 ≢ zero9
tfix-ne-v20 ()
tfix-ne-v22 : tfix v22 ≢ zero9
tfix-ne-v22 ()
tfix-ne-v23 : tfix v23 ≢ zero9
tfix-ne-v23 ()
tfix-ne-v30 : tfix v30 ≢ zero9
tfix-ne-v30 ()
tfix-ne-v31 : tfix v31 ≢ zero9
tfix-ne-v31 ()
tfix-ne-v32 : tfix v32 ≢ zero9
tfix-ne-v32 ()
tfix-ne-v33 : tfix v33 ≢ zero9
tfix-ne-v33 ()
