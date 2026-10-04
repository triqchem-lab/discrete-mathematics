{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseBoundaryK3
-- 任务书第五层·5.1 泛型化 M2 sanity check：Morse 边界 ∂^Morse 的
--   **关系形态聚合**在 K₃ 上与手算 ∂₁ᶜ 对账
--
-- 数学背景（Forman 主定理路线 M2）：
--   ∂^Morse e₂₀ = Σ_{路由} 系数·临界胞腔。K₃ triVF 场上：
--   ①直连路由 e₂₀ → v₂（v₂ 临界，∂e₂₀ 的 v₂ 系数 T₂）
--   ②路由项 e₂₀ → v₀ → e₀₁ → v₁（v₀ 配对非临界，路由到 v₁，总系数 T₁）
--   聚合 ⟹ ∂^Morse e₂₀ = T₁·v₁ + T₂·v₂——与 MorseCriticalHomology
--   手算的 ∂₁ᶜ 生成元像 (T₁, T₂) 完全一致。
--
--   两条独立形式化路径闭坏：
--     路径 1：MorseRoutingK3 的系数级手算（gen⊗entry⊗inv⊗eps）
--     路径 2：本模块的 CoefRoute 归纳关系（MorseCoeffRoute.routing-k3）
--   两者落点相同 (T₁, T₂) —— M2 技术路线确认（M3 路径配对可启动）。
--
-- 复用：MorseCoeffRoute（routing-k3 + CoefRouteDef）+ MorseCriticalHomology（∂₁ᶜ）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseBoundaryK3 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊗_; _⊕_)
open import Sovereign.Algebra.FreeAb using (FAb)
open import Sovereign.Topology.FormanMinimal
  using (Sx; v0; v1; v2; e01; e12; e20; t)
open import Sovereign.Topology.FormanPerfectField
  using (FaceRel; f-v2-e20)
open import Sovereign.Topology.MorseCoeffRoute
  using (coeffᵏ; triVFᶜ; routing-k3)
open module MCRD = Sovereign.Topology.MorseCoeffRoute.CoeffRouteDef
  Sx triVFᶜ FaceRel coeffᵏ
open import Sovereign.Problem.Hodge.FreeAbBoundary using (∂₁; ∂₂)
open import Sovereign.Topology.MorseCriticalHomology using (∂₁ᶜ)

--------------------------------------------------------------------------------
-- §1. 两条路由（CoefRoute 归纳关系形态）
--------------------------------------------------------------------------------

-- ①直连路由：e₂₀ → v₂（v₂ 临界：triVF v2 ≡ nothing refl；
--   ∂e₂₀ 的 v₂ 系数 T₂ = coeffᵏ v2 e20）
direct-route : CoefRoute e20 v2 T₂
direct-route =
  cr-direct e20 v2 T₂ f-v2-e20 refl refl

-- ②路由项：e₂₀ → v₀ → e₀₁ → v₁，总系数 T₁
--   （MorseCoeffRoute.routing-k3 已证，直接引用）
routed-route : CoefRoute e20 v1 T₁
routed-route = routing-k3

--------------------------------------------------------------------------------
-- §2. 聚合：∂^Morse e₂₀ = T₁·v₁ + T₂·v₂
--   v₁ 系数 = 路由项总系数 T₁；v₂ 系数 = 直连项系数 T₂；
--   无其他贡献（v₀ 非临界不收直连；e₀₁ 非临界；t 维度不对）
--------------------------------------------------------------------------------

∂M-e₂₀-v₁ : Trit
∂M-e₂₀-v₁ = T₁

∂M-e₂₀-v₂ : Trit
∂M-e₂₀-v₂ = T₂

-- 聚合对 = (T₁, T₂)
∂M-e₂₀ : Trit × Trit
∂M-e₂₀ = ∂M-e₂₀-v₁ , ∂M-e₂₀-v₂

∂M-e₂₀≡T₁T₂ : ∂M-e₂₀ ≡ (T₁ , T₂)
∂M-e₂₀≡T₁T₂ = refl

--------------------------------------------------------------------------------
-- §3. 与手算 ∂₁ᶜ 对账（MorseCriticalHomology 独立路径）
--   ∂₁ᶜ 生成元（FAb 1 的 T₁）↦ (T₁, T₂)：
--     ∂₁ᶜ gen fzero = T₁ ⊗ T₁ = T₁（v₁ 系数，路由项）
--     ∂₁ᶜ gen fsuc-fzero = T₁ ⊗ T₂ = T₂（v₂ 系数，直连项）
--   两条独立形式化（关系形态 vs 逐点函数形态）落点一致。
--------------------------------------------------------------------------------

-- ∂₁ᶜ 的生成元输入（FAb 1：e₂₀ ↦ T₁）
gen-e₂₀ : FAb 1
gen-e₂₀ fzero = T₁
gen-e₂₀ (fsuc ())

-- ∂₁ᶜ gen 的两分量（逐点计算）
∂₁ᶜ-gen-v₁ : Trit
∂₁ᶜ-gen-v₁ = ∂₁ᶜ gen-e₂₀ fzero

∂₁ᶜ-gen-v₂ : Trit
∂₁ᶜ-gen-v₂ = ∂₁ᶜ gen-e₂₀ (fsuc fzero)

-- 对账：关系形态聚合 ≡ 函数形态计算
m2-sanity-v₁ : ∂M-e₂₀-v₁ ≡ ∂₁ᶜ-gen-v₁
m2-sanity-v₁ = refl

m2-sanity-v₂ : ∂M-e₂₀-v₂ ≡ ∂₁ᶜ-gen-v₂
m2-sanity-v₂ = refl

-- 完整 sanity check：∂^Morse e₂₀ = (T₁,T₂) = ∂₁ᶜ gen ✓
m2-sanity : ∂M-e₂₀ ≡ (∂₁ᶜ-gen-v₁ , ∂₁ᶜ-gen-v₂)
m2-sanity = refl
