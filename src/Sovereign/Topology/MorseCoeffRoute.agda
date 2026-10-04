{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseCoeffRoute
-- 任务书第五层·5.1 泛型化第二块：**系数簿记 + 临界判定路由**
--
-- 数学背景：代数 Morse 边界的完整路由——每条交替路径携带**系数乘积**
--   μ(path) = (∂ 项系数) × (入口系数)⁻¹ × (出口系数) × ε，
--   且路由**终止于临界单形**（V τ ≡ nothing）。
--
--   本模块给出 GF(3) 系数版：
--   ①MorseCoeffField record——在 MorseFieldG 基础上加 coeff 系数函数
--     与 entry-inv（配对入口系数的逆，GF(3) 域性封装）
--   ②CoeffRoute 归纳关系——系数为索引的归纳路由：
--     cr-direct 带**临界终止判定**（V τ ≡ nothing）；
--     cr-via 带系数复合（μ_in ⊗ i ⊗ (T₂ ⊗ ν)，T₂ = ε 一次 V-箭头）
--   ③维度下降（系数版同构于 MorseRoute 版）
--   ④K₃ 实例：非完美场路由 e₂₀→v₀→e₀₁→v₁ 总系数 T₁ ≡ ∂₁ᶜ 的 v₁ 系数
--
-- 复用：Algebra.FreeAb（无关但同线）、Base/Trit 算术、MorseRoute（降维模式）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseCoeffRoute where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)
open import Data.Nat.Properties using (<-≤-trans)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊗_)
open import Sovereign.Topology.MorseRoute using (MorseFieldG)

--------------------------------------------------------------------------------
-- §1. MorseCoeffField record（GF(3) 系数版泛型场）
--------------------------------------------------------------------------------

record MorseCoeffField (K : Set) (dimK : K → ℕ) : Set₁ where
  field
    Face     : K → K → Set
    face-dim : ∀ τ σ → Face τ σ → dimK τ < dimK σ
    coeff    : K → K → Trit                   -- coeff τ σ：∂σ 的 τ 系数
    V        : K → Maybe K
    dim-law  : ∀ σ τ → V σ ≡ just τ → dimK τ ≡ suc (dimK σ)
    -- 配对入口系数的逆（GF(3) 域性封装：非零 ⟹ 逆存在）
    entry-inv : ∀ w e' → V w ≡ just e' →
                Σ Trit (λ i → coeff w e' ⊗ i ≡ T₁)

--------------------------------------------------------------------------------
-- §2. 系数路由关系（临界终止 + 系数复合）
--------------------------------------------------------------------------------

module CoeffRouteDef
  (K : Set) (V : K → Maybe K) (Face : K → K → Set)
  (coeff : K → K → Trit) where

  -- 系数索引的归纳路由：CoefRoute σ τ μ 读作 ∂^Morse σ 在 τ 上的系数为 μ
  data CoefRoute : K → K → Trit → Set where
    -- 临界终止判定：直连项只写入**临界**单形（V τ ≡ nothing）
    cr-direct : ∀ σ τ μ → Face τ σ → coeff τ σ ≡ μ → V τ ≡ nothing →
                CoefRoute σ τ μ
    -- 经配对路由：总系数 = μ_in ⊗ i ⊗ (T₂ ⊗ ν)
    --   （μ_in = 入段系数，i = 入口逆，T₂ = ε 一次 V-箭头，ν = 尾段总系数）
    cr-via    : ∀ σ w e' τ μ-in i ν →
                Face w σ → V w ≡ just e' → Face τ e' →
                coeff w σ ≡ μ-in → coeff w e' ⊗ i ≡ T₁ →
                CoefRoute e' τ ν →
                CoefRoute σ τ ((μ-in ⊗ i) ⊗ (T₂ ⊗ ν))

--------------------------------------------------------------------------------
-- §3. 维度下降（系数版——与 MorseRoute.route-dim-descent 同构）
--------------------------------------------------------------------------------

module CoeffDescent (K : Set) (dimK : K → ℕ)
  (V : K → Maybe K) (Face : K → K → Set) (coeff : K → K → Trit)
  (face-dim : ∀ τ σ → Face τ σ → dimK τ < dimK σ)
  (dim-law : ∀ σ τ → V σ ≡ just τ → dimK τ ≡ suc (dimK σ)) where

  open CoeffRouteDef K V Face coeff

  coeff-dim-descent : ∀ σ τ μ → CoefRoute σ τ μ → dimK τ < dimK σ
  coeff-dim-descent σ τ μ (cr-direct .σ .τ .μ hface hcoef hcrit) =
    face-dim τ σ hface
  coeff-dim-descent σ τ μ
    (cr-via .σ w e' .τ μ-in i ν hface hw hp hcoef hinv hroute) =
      <-≤-trans τ<e' e'≤σ
    where
      τ<e' : dimK τ < dimK e'
      τ<e' = face-dim τ e' hp

      e'≡suc-w : dimK e' ≡ suc (dimK w)
      e'≡suc-w = dim-law w e' hw

      e'≤σ : dimK e' ≤ dimK σ
      e'≤σ = subst (λ z → z ≤ dimK σ) (sym e'≡suc-w) (face-dim w σ hface)

--------------------------------------------------------------------------------
-- §4. K₃ 实例：非完美场 triVF 的路由系数（对照 ∂₁ᶜ）
--------------------------------------------------------------------------------

open import Sovereign.Topology.FormanMinimal
  using (Sx; v0; v1; v2; e01; e12; e20; t)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Sovereign.Topology.FormanPerfectField
  using (FaceRel; f-v0-e20; f-v1-e01; f-v2-e12;
         f-v0-e01; f-v2-e20; f-e01-t; f-e12-t; f-e20-t)

-- ∂ 系数表（来源：FreeAbBoundary 定向约定）
coeffᵏ : Sx → Sx → Trit
coeffᵏ v0 e20 = T₁
coeffᵏ v2 e20 = T₂
coeffᵏ v1 e01 = T₁
coeffᵏ v0 e01 = T₂
coeffᵏ e01 t = T₁
coeffᵏ e12 t = T₁
coeffᵏ e20 t = T₁
coeffᵏ _ _ = T₀

triVFᶜ : Sx → Maybe Sx
triVFᶜ v0 = just e01
triVFᶜ v1 = nothing
triVFᶜ v2 = nothing
triVFᶜ e01 = nothing
triVFᶜ e12 = just t
triVFᶜ e20 = nothing
triVFᶜ t = nothing

-- 配对入口逆（v0↔e01：coeff v0 e01 = T₂，逆 = T₂：T₂⊗T₂ ≡ T₁）
entry-inv-k3 : Σ Trit (λ i → coeffᵏ v0 e01 ⊗ i ≡ T₁)
entry-inv-k3 = T₂ , refl

-- 路由见证：e₂₀ → v₀ → e₀₁ → v₁，总系数 T₁
--  （v₁ 临界：triVF v1 ≡ nothing；逐项：Face v0 e₂₀ = f-v0-e₂₀ ✓ 等）
open CoeffRouteDef Sx triVFᶜ FaceRel coeffᵏ

routing-k3 : CoefRoute e20 v1 T₁
routing-k3 =
  cr-via e20 v0 e01 v1 T₁ T₂ T₁
    f-v0-e20 refl f-v1-e01
    refl refl
    (cr-direct e01 v1 T₁ f-v1-e01 refl refl)
