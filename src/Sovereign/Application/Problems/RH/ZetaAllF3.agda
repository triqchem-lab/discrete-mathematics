{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.ZetaAllF3
-- zeta 函数方程与零点刚性的 F₃ 全称化（M1 · A1.7b）
--
-- 数学背景:
--   L(T) = 1 − tT + 3T², Z(T) = L(T)/((1−T)(1−3T))。
--   · 函数方程 Z(1/3T) = Z(T) 对**任意迹 t** 成立（genus-1 恒等式）:
--     交叉相乘形式 recipClear(3,L)·D ≡ L·recipClear(3,D) 是 t 的符号恒等式,
--     本文件对 Tr3 的 7 值逐值 refl（§2 的 18 曲线版经 CountF3.tℤ 闭包归约）。
--   · 零点刚性 α⁻¹, β⁻¹ 为零点（即 P*(α) = 0）在 ℤ[ω] 内的承载**只对超奇异
--     曲线成立**（q=p 时 α ∈ ℤ[ω] ⟺ 3 ∣ t）: t=0,±3 的 α = (t+s√−3)/2 ∈ ℤ[ω]
--     由 WeilRigidity 三组见证给出；普通曲线（t=±1,±2）的特征多项式判别式
--     t²−12 = −11 / −8，特征值落在 ℚ(√−11)/ℚ(√−2)/ℚ(i)，不在 ℤ[ω]
--     （此解读为文档层注记，未形式化；与 NoNormT0Even 的投影域失配一致）。
--
-- 陈述:
--   FuncEq c      := recipClear 3 (Zpoly (tℤ c) 3) *q denPoly 3
--                 ≡ Zpoly (tℤ c) 3 *q recipClear 3 (denPoly 3)
--   fe-cross-val  : ∀ (v : Tr3) → FuncEq (val v) 的逐值版（7 refl）
--   fe-cross-all  : ∀ c → IsNonSing c → FuncEq c（**∀④**，27 构造子分派）
--   RigE c        := Σ Eisenstein (λ α → (α +ᵉ conjᵉ α ≡ eis (tℤ c) (+ 0))
--                                      × (α *ᵉ conjᵉ α ≡ 3ᵉ))
--   zero-rig-sup  : ∀ c → IsNonSing c → IsSup c → RigE c（**∀⑤**，超奇异 6 条；
--     见证复用 WeilRigidity 的 alpha-E1/E2/E6 三组——t 相同则 α 相同, 定义性替换）
--
-- 复用: ZetaFrame（A1.7a 提取的公共框架）、WeilRigidity（三组 ℤ[ω] 刚性见证）、
--   SupersingularF3.IsSup（可判定超奇异性）。
-- 0 postulate，全部 refl / λ() / ⊥-elim。

module Sovereign.Application.Problems.RH.ZetaAllF3 where

open import Data.Empty using (⊥-elim)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Foundation.Eisenstein
  using (Eisenstein; eis; 0ᵉ; 3ᵉ; _+ᵉ_; _*ᵉ_; conjᵉ)
open import Sovereign.Application.Problems.RH.CurveF3
open import Sovereign.Application.Problems.RH.CountF3
open import Sovereign.Application.Problems.RH.ZetaFrame
  using (Quad; recipClear; _*q_; Zpoly; denPoly)
open import Sovereign.Application.Problems.RH.TraceTableF3
open import Sovereign.Application.Problems.RH.SupersingularF3
open import Sovereign.Application.Problems.RH.WeilRigidity
  using (alpha-E1; alpha-E2; alpha-E6;
         trace-sum-E1; trace-sum-E2; trace-sum-E6;
         norm-product-E1; norm-product-E2; norm-product-E6)

--------------------------------------------------------------------------------
-- §1. 函数方程的逐值版（Tr3 的 7 值, 各 refl）
--------------------------------------------------------------------------------

fe-cross-val : ∀ (v : Tr3) →
  recipClear (+ 3) (Zpoly (val v) (+ 3)) *q denPoly (+ 3)
  ≡ Zpoly (val v) (+ 3) *q recipClear (+ 3) (denPoly (+ 3))
fe-cross-val trM3 = refl
fe-cross-val trM2 = refl
fe-cross-val trM1 = refl
fe-cross-val trZ  = refl
fe-cross-val trP1 = refl
fe-cross-val trP2 = refl
fe-cross-val trP3 = refl

--------------------------------------------------------------------------------
-- §2. **∀④** 函数方程: 全部 18 条非奇异曲线
--------------------------------------------------------------------------------

FuncEq : CurveF3 → Set
FuncEq c =
  recipClear (+ 3) (Zpoly (tℤ c) (+ 3)) *q denPoly (+ 3)
  ≡ Zpoly (tℤ c) (+ 3) *q recipClear (+ 3) (denPoly (+ 3))

fe-cross-all : ∀ (c : CurveF3) → IsNonSing c → FuncEq c
fe-cross-all (mkC T₀ T₀ T₀) h = ⊥-elim (h refl)
fe-cross-all (mkC T₀ T₀ T₁) h = ⊥-elim (h refl)
fe-cross-all (mkC T₀ T₀ T₂) h = ⊥-elim (h refl)
fe-cross-all (mkC T₀ T₁ T₀) h = refl   -- t = 0
fe-cross-all (mkC T₀ T₁ T₁) h = refl   -- t = 0
fe-cross-all (mkC T₀ T₁ T₂) h = refl   -- t = 0
fe-cross-all (mkC T₀ T₂ T₀) h = refl   -- t = 0
fe-cross-all (mkC T₀ T₂ T₁) h = refl   -- t = −3
fe-cross-all (mkC T₀ T₂ T₂) h = refl   -- t = +3
fe-cross-all (mkC T₁ T₀ T₀) h = ⊥-elim (h refl)
fe-cross-all (mkC T₁ T₀ T₁) h = refl   -- t = −2
fe-cross-all (mkC T₁ T₀ T₂) h = refl   -- t = +1
fe-cross-all (mkC T₁ T₁ T₀) h = ⊥-elim (h refl)
fe-cross-all (mkC T₁ T₁ T₁) h = refl   -- t = −2
fe-cross-all (mkC T₁ T₁ T₂) h = refl   -- t = +1
fe-cross-all (mkC T₁ T₂ T₀) h = refl   -- t = −2
fe-cross-all (mkC T₁ T₂ T₁) h = refl   -- t = +1
fe-cross-all (mkC T₁ T₂ T₂) h = ⊥-elim (h refl)
fe-cross-all (mkC T₂ T₀ T₀) h = ⊥-elim (h refl)
fe-cross-all (mkC T₂ T₀ T₁) h = refl   -- t = −1
fe-cross-all (mkC T₂ T₀ T₂) h = refl   -- t = +2
fe-cross-all (mkC T₂ T₁ T₀) h = ⊥-elim (h refl)
fe-cross-all (mkC T₂ T₁ T₁) h = refl   -- t = −1
fe-cross-all (mkC T₂ T₁ T₂) h = refl   -- t = +2
fe-cross-all (mkC T₂ T₂ T₀) h = refl   -- t = +2
fe-cross-all (mkC T₂ T₂ T₁) h = ⊥-elim (h refl)
fe-cross-all (mkC T₂ T₂ T₂) h = refl   -- t = −1

--------------------------------------------------------------------------------
-- §3. **∀⑤** 零点刚性（ℤ[ω] 承载）: 超奇异 6 条
--------------------------------------------------------------------------------

RigE : CurveF3 → Set
RigE c = Σ Eisenstein (λ α →
  (α +ᵉ conjᵉ α ≡ eis (tℤ c) (+ 0)) × (α *ᵉ conjᵉ α ≡ 3ᵉ))

zero-rig-sup : ∀ (c : CurveF3) → IsNonSing c → IsSup c → RigE c
-- 奇异 9 支（6 支 ⊤: t=0 用 alpha-E1 组; 3 支 ⊥ 吸收）
zero-rig-sup (mkC T₀ T₀ T₀) h s = ( alpha-E1 , trace-sum-E1 , norm-product-E1 )  -- #E=4, t=0
zero-rig-sup (mkC T₀ T₀ T₁) h s = ( alpha-E1 , trace-sum-E1 , norm-product-E1 )  -- #E=4, t=0
zero-rig-sup (mkC T₀ T₀ T₂) h s = ( alpha-E1 , trace-sum-E1 , norm-product-E1 )  -- #E=4, t=0
zero-rig-sup (mkC T₁ T₀ T₀) h s = ⊥-elim s    -- 奇异, SupV ⊥
zero-rig-sup (mkC T₁ T₁ T₀) h s = ⊥-elim s    -- 奇异, SupV ⊥
zero-rig-sup (mkC T₁ T₂ T₂) h s = ⊥-elim s    -- 奇异, SupV ⊥
zero-rig-sup (mkC T₂ T₀ T₀) h s = ⊥-elim s    -- 奇异, SupV ⊥
zero-rig-sup (mkC T₂ T₁ T₀) h s = ⊥-elim s    -- 奇异, SupV ⊥
zero-rig-sup (mkC T₂ T₂ T₁) h s = ⊥-elim s    -- 奇异, SupV ⊥
-- 非奇异超 6 支: t=0（4 条）用 alpha-E1 组; t=−3 用 alpha-E2 组; t=+3 用 alpha-E6 组
zero-rig-sup (mkC T₀ T₁ T₀) h s = ( alpha-E1 , trace-sum-E1 , norm-product-E1 )  -- t = 0
zero-rig-sup (mkC T₀ T₁ T₁) h s = ( alpha-E1 , trace-sum-E1 , norm-product-E1 )  -- t = 0
zero-rig-sup (mkC T₀ T₁ T₂) h s = ( alpha-E1 , trace-sum-E1 , norm-product-E1 )  -- t = 0
zero-rig-sup (mkC T₀ T₂ T₀) h s = ( alpha-E1 , trace-sum-E1 , norm-product-E1 )  -- t = 0
zero-rig-sup (mkC T₀ T₂ T₁) h s = ( alpha-E2 , trace-sum-E2 , norm-product-E2 )  -- t = −3
zero-rig-sup (mkC T₀ T₂ T₂) h s = ( alpha-E6 , trace-sum-E6 , norm-product-E6 )  -- t = +3
-- 非奇异普通 12 支: SupV ⊥ 吸收
zero-rig-sup (mkC T₁ T₀ T₁) h s = ⊥-elim s    -- t = −2
zero-rig-sup (mkC T₁ T₀ T₂) h s = ⊥-elim s    -- t = +1
zero-rig-sup (mkC T₁ T₁ T₁) h s = ⊥-elim s    -- t = −2
zero-rig-sup (mkC T₁ T₁ T₂) h s = ⊥-elim s    -- t = +1
zero-rig-sup (mkC T₁ T₂ T₀) h s = ⊥-elim s    -- t = −2
zero-rig-sup (mkC T₁ T₂ T₁) h s = ⊥-elim s    -- t = +1
zero-rig-sup (mkC T₂ T₀ T₁) h s = ⊥-elim s    -- t = −1
zero-rig-sup (mkC T₂ T₀ T₂) h s = ⊥-elim s    -- t = +2
zero-rig-sup (mkC T₂ T₁ T₁) h s = ⊥-elim s    -- t = −1
zero-rig-sup (mkC T₂ T₁ T₂) h s = ⊥-elim s    -- t = +2
zero-rig-sup (mkC T₂ T₂ T₀) h s = ⊥-elim s    -- t = +2
zero-rig-sup (mkC T₂ T₂ T₂) h s = ⊥-elim s    -- t = −1
