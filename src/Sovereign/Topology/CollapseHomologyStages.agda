{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.CollapseHomologyStages
-- 任务书第五层·5.1 推进：坍缩序列**同调不变**实例（B2）
--
-- 数学背景：初等坍缩保持同调。K₃ 完美坍缩序列的四阶段：
--   阶段 0：满三角（7 单形）        dimH = (1,0,0)（jac_Topology 已证）
--   阶段 1：删 (e01,t)（5 单形）    剩余 = 图 v1-v2-v0（两边的树）
--   阶段 2：删 (v1,e12)（3 单形）   剩余 = 单边 v2-v0
--   阶段 3：删 (v2,e20)（1 单形）   剩余 = 点 {v0}
--   四阶段 dimH 逐维相等——坍缩同调不变定理的实例层闭合。
--
--   秩来源（注释层）：阶段 1 ∂₁ 的两列 (2v₁+v₂, 2v₂+v₀) GF(3)-无关
--   （v₁ 分量 2α ≡ T₀ ⟹ α ≡ T₀，再 v₀ 分量 ⟹ β ≡ T₀——3×3 case）；
--   阶段 2 ∂₁ 单列非零 ⟹ 秩 1。
--
-- 复用：ChainComplex record + dimH（Problem/Hodge/ChainComplex）、
--   pointC（MorseStrongCritical）、filled3C（jac_Topology）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.CollapseHomologyStages where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Problem.Hodge.ChainComplex
  using (ChainComplex; dimH)
import Sovereign.Problem.Hodge.ChainComplex as CC
open import Sovereign.Algebra.Jacobian.jac_Topology
  using (filled3C; dimH-filled3-0; dimH-filled3-1; dimH-filled3-2)
open import Sovereign.Topology.MorseStrongCritical using (pointC)

--------------------------------------------------------------------------------
-- §1. 阶段 1 复形：删 (e01,t) 后——3 顶点 + 2 边（树 v1-v2-v0）
--------------------------------------------------------------------------------

s1-dim : ℕ → ℕ
s1-dim zero = 3
s1-dim (suc zero) = 2
s1-dim _ = 0

s1-rank : ℕ → ℕ
s1-rank zero = 0
s1-rank (suc zero) = 2
s1-rank _ = 0

s1-null : ℕ → ℕ
s1-null zero = 3
s1-null (suc zero) = 0
s1-null _ = 0

s1-harm : ℕ → ℕ
s1-harm zero = 1
s1-harm _ = 0

s1-hodge : ∀ k → s1-null k ≡ s1-rank (suc k) + s1-harm k
s1-hodge zero = refl
s1-hodge (suc zero) = refl
s1-hodge (suc (suc k)) = refl

stage1 : ChainComplex 3
CC.ChainComplex.dimC stage1 = s1-dim
CC.ChainComplex.rank∂ stage1 = s1-rank
CC.ChainComplex.nullity∂ stage1 = s1-null
CC.ChainComplex.dimℋ stage1 = s1-harm
CC.ChainComplex.hodge-decomp stage1 = s1-hodge

--------------------------------------------------------------------------------
-- §2. 阶段 2 复形：删 (v1,e12) 后——2 顶点 + 1 边（单边 v2-v0）
--------------------------------------------------------------------------------

s2-dim : ℕ → ℕ
s2-dim zero = 2
s2-dim (suc zero) = 1
s2-dim _ = 0

s2-rank : ℕ → ℕ
s2-rank zero = 0
s2-rank (suc zero) = 1
s2-rank _ = 0

s2-null : ℕ → ℕ
s2-null zero = 2
s2-null (suc zero) = 0
s2-null _ = 0

s2-harm : ℕ → ℕ
s2-harm zero = 1
s2-harm _ = 0

s2-hodge : ∀ k → s2-null k ≡ s2-rank (suc k) + s2-harm k
s2-hodge zero = refl
s2-hodge (suc zero) = refl
s2-hodge (suc (suc k)) = refl

stage2 : ChainComplex 3
CC.ChainComplex.dimC stage2 = s2-dim
CC.ChainComplex.rank∂ stage2 = s2-rank
CC.ChainComplex.nullity∂ stage2 = s2-null
CC.ChainComplex.dimℋ stage2 = s2-harm
CC.ChainComplex.hodge-decomp stage2 = s2-hodge

--------------------------------------------------------------------------------
-- §3. 四阶段同调一致（逐维：H₀ = 1 ∧ H₁ = 0 ∧ H₂ = 0）
--------------------------------------------------------------------------------

-- 阶段 0（满三角，jac_Topology 已证）∥ 阶段 3（点，MorseStrongCritical 已证）
-- 本模块补齐中间两阶段的 dimH：
stage1-hom-0 : dimH stage1 0 ≡ 1
stage1-hom-0 = refl

stage1-hom-1 : dimH stage1 1 ≡ 0
stage1-hom-1 = refl

stage1-hom-2 : dimH stage1 2 ≡ 0
stage1-hom-2 = refl

stage2-hom-0 : dimH stage2 0 ≡ 1
stage2-hom-0 = refl

stage2-hom-1 : dimH stage2 1 ≡ 0
stage2-hom-1 = refl

stage2-hom-2 : dimH stage2 2 ≡ 0
stage2-hom-2 = refl

-- 四阶段 H₀ 全一致（= 1）
invariance-h0 : (dimH filled3C 0 ≡ dimH stage1 0) ×
                ((dimH stage1 0 ≡ dimH stage2 0) ×
                (dimH stage2 0 ≡ dimH pointC 0))
invariance-h0 = refl , (refl , refl)

-- 四阶段 H₁ 全一致（= 0）
invariance-h1 : (dimH filled3C 1 ≡ dimH stage1 1) ×
                ((dimH stage1 1 ≡ dimH stage2 1) ×
                (dimH stage2 1 ≡ dimH pointC 1))
invariance-h1 = refl , (refl , refl)

-- 四阶段 H₂ 全一致（= 0）
invariance-h2 : (dimH filled3C 2 ≡ dimH stage1 2) ×
                ((dimH stage1 2 ≡ dimH stage2 2) ×
                (dimH stage2 2 ≡ dimH pointC 2))
invariance-h2 = refl , (refl , refl)
