{-# OPTIONS --rewriting --guardedness #-}

{- | Sovereign.Application.DiscreteHodgeDecomposition

  Dodziuk 组合 Hodge 分解面（任务书 v2.0 §4.3——P3 随缘尾件）。

  数学背景：Dodziuk 1976 证明组合 Laplacian 收敛到连续 Laplacian
  （连续逼近面）——**本框架主张：离散充足**，但 Dodziuk 原定理是
  **逼近**而非替代（诚实边界——本件只做施工面，替代主张 D3 报告独立走）。

  本件（与 EckmannGF3/EckmannNonSplitting 零重证衔接）：
  - EckmannGF3 的**失正定内积** has isotropic: NonZero isotropic 且
    inner isotropic isotropic ≡ T₀（C⁰ 面 surprisingly 全最高的失正定面）
  - harmonic 面在此承载下有 : nullNotZero companion （真实向量，非零）
-}

module Sovereign.Application.DiscreteHodgeDecomposition where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_; id)

open import Data.Sum using (_⊎_; inj₁; inj₂)
-- 基础单元直引（EckmannGF3 零重证——真实符号面：V3/isotropic/nullNotZero）
open import Sovereign.Application.EckmannGF3
  using (V3; NonZero; isotropic; isotropic-nonzero; isotropic-null;
         null-not-zero; zeroV; inner)

--------------------------------------------------------------------------------
-- §0 基础件：NonZero 分叉分派（EckmannGF3 :55-57 的 Σ/⊎ 结构面）
--
-- NonZero 的三支结构（逐位 ≢ T₀）给 harmonic 面统计能力的**独立承载面**
--------------------------------------------------------------------------------

-- 零向量（全 T₀）—— NonZero 破面（真实零向量）
zeroV3 : V3
zeroV3 = zeroV

zeroV-not-nonzero : NonZero zeroV3 → ⊥
zeroV-not-nonzero (inj₁ h) = h refl
zeroV-not-nonzero (inj₂ (inj₁ h)) = h refl
zeroV-not-nonzero (inj₂ (inj₂ h)) = h refl

-- 恒等内积约束（isotropic = (1,1,1) 的 self 内积 = T₀）
-- EckmannGF3 失正定面（verify this：isotropic-null 直引——一等 **调和** 代表）
hodge0 : Σ[ u ∈ V3 ] (NonZero u × (inner u u ≡ _))
hodge0 = null-not-zero

hodge0-nonzero : NonZero (proj₁ hodge0)
hodge0-nonzero = proj₁ (proj₂ hodge0)

-- §1 核对层（具体点对抗）
--------------------------------------------------------------------------------

-- 核对（isotropic 的真实点地位）
check-isotropic-nonzero : NonZero isotropic
check-isotropic-nonzero = isotropic-nonzero

check-isotropic-null : inner isotropic isotropic ≡ _
check-isotropic-null = isotropic-null

-- §2 立界注记（本件不越界主张）
--    - Dodziuk 收敛/替代面的完整论证 → D3 研究报告（酸奶律.note）独立走
--    - HodgeDecomp 的 decomp-orth 域（正定内积面）→ 待 EckmannNonSplitting
--      的分解骨架对之后施工（WIP 注记可编译面全在）
--    - 完整 Eckmann 分解 / 不分裂 ∂/δ 矩阵链（EckmannGF3 :19-20 roadmap）
--      — → **Issue: 一个里程文档级调查——本件优先级缩为施工面任务**
--------------------------------------------------------------------------------

-- [WIP: HodgeDecomp record 的 decomp-orth 待 EckmannNonSplitting 分解骨架
--  对接（立界不走暗示不硬拱 —— D3 报告产面结论独立）。可编译部分保留。]
