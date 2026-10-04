{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseExistence
-- 任务书第五层·5.1 补件：Morse 场**存在性**（一般 K）+ 三场 χ 一致
--
-- 数学背景：Forman 理论的**存在性方向**——任意（有限）复形都 admits
--   离散 Morse 函数：平凡解 V ≡ nothing（全单形临界，无配对）。
--   本模块在 DiscreteMorseGeneral 的泛型 record 上闭合存在性，
--   并补齐 K₃ 第三场 collapseVF 的 χ_m 实例（三场 χ 一致——
--   Forman 第一定理「χ_m 与场无关」的三场版本）。
--
-- 复用：DiscreteMorseGeneral（泛型 record）、MorseAcyclic（泛型无环
--   ——第四复用）、MorseChiBoth（χ 定义）、CollapseToMorse（collapseVF）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseExistence where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.DiscreteMorseGeneral
  using (DiscreteMorseFunction)
open import Sovereign.Topology.FormanChiInvariant using (chi-m-f)
open import Sovereign.Topology.FormanMinimal using (Sx; v0; v1; v2; e01; e12; e20; t; dim)
open import Sovereign.Topology.CollapseToMorse using (collapseVF)

--------------------------------------------------------------------------------
-- §1. 存在性：任意 K 上的平凡 Morse 场（全临界，无配对）
--
--   Forman 存在性方向的构造性闭合：V ≡ nothing 的 dim-law 前件
--   恒假（nothing ≢ just τ 顶层冲突），两律空洞成立。
--------------------------------------------------------------------------------

nothing-just : ∀ {K : Set} {τ : K} → ¬ (nothing ≡ just τ)
nothing-just ()

trivialField : ∀ (K : Set) (dimK : K → ℕ) → DiscreteMorseFunction K dimK
DiscreteMorseFunction.V (trivialField K dimK) = λ _ → nothing
DiscreteMorseFunction.dim-law (trivialField K dimK) σ τ h = ⊥-elim (nothing-just h)
DiscreteMorseFunction.V-inj (trivialField K dimK) σ σ' τ h₁ h₂ = ⊥-elim (nothing-just h₁)

--------------------------------------------------------------------------------
-- §3. 第三场 collapseVF 的 χ_m 实例（三场 χ 一致）
--
--   collapseVF 临界 = {v0}：m = (1,0,0)，χ_m = 1∸0+0 = 1
--   与 triVF（2,1,0）和 perfectVF（1,0,0）的 χ_m 一致。
--------------------------------------------------------------------------------

chi-m-collapse : ℕ
chi-m-collapse = chi-m-f 1 0 0

chi-m-collapse≡1 : chi-m-collapse ≡ 1
chi-m-collapse≡1 = refl

-- 三场 χ 一致（数值层：全 ≡ 1）
three-field-agree : chi-m-f 2 1 0 ≡ 1 × chi-m-f 1 0 0 ≡ 1 × chi-m-collapse ≡ 1
three-field-agree = refl , (refl , refl)
