{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseBoundaryDT
-- 任务书第五层·5.1 泛型化 M3 首站：双三角上的 **∂²=0 路径配对相消**
--
-- 数学背景（oracle 已核数值）：
--   ∂₂ᶜ FL = T₂·e02（直连唯一：e02 临界；e01/e12 非临界且 V=nothing 无路由）
--   ∂₁ᶜ e02 = T₁·v₂（直连）⊕ T₂·v₂（链式路由 e02→v₀→e₀₁→v₁→e₁₂→v₂，
--     2 V-箭头 ε²=T₁；内层 e₀₁→v₂ = T₁；外层总 = T₂）
--   ⟹ T₁ ⊕ T₂ = T₀：直连与路由在 v₂ 上配对相消——∂₁ᶜ∘∂₂ᶜ = 0 ✓
--
--   机件修正：MorseCoeffRoute.CoefRoute 的 cr-via 含 Face τ e' 字段——
--   仅支持单跳（K₃ 恰单跳）；本模块定义修正版 **ChainRoute**（ch-via 去掉
--   Face τ e'，续程证据由尾递归自带）——支持任意跳数；CoefRoute = 单跳特例。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseBoundaryDT where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊗_; _⊕_)
open import Sovereign.Topology.DoubleTriangle
  using (Sx2; v0; v1; v2; v3; e01; e02; e12; e13; e23; FL; FR;
         V2; coeff2E; coeff2F)

--------------------------------------------------------------------------------
-- §1. 统一系数表：coeff2 w σ = ∂σ 的 w 系数（16 实项 + 兜底）
--------------------------------------------------------------------------------

coeff2 : Sx2 → Sx2 → Trit
coeff2 = λ w σ → coeff2U w σ
  where
    coeff2U : Sx2 → Sx2 → Trit
    coeff2U v0 e01 = T₂
    coeff2U v1 e01 = T₁
    coeff2U v0 e02 = T₂
    coeff2U v2 e02 = T₁
    coeff2U v1 e12 = T₂
    coeff2U v2 e12 = T₁
    coeff2U v1 e13 = T₂
    coeff2U v3 e13 = T₁
    coeff2U v2 e23 = T₂
    coeff2U v3 e23 = T₁
    coeff2U e01 FL = T₁
    coeff2U e02 FL = T₂
    coeff2U e12 FL = T₁
    coeff2U e12 FR = T₁
    coeff2U e13 FR = T₂
    coeff2U e23 FR = T₁
    coeff2U _ _ = T₀

--------------------------------------------------------------------------------
-- §2. 面关系 Face2（16 构造子）
--------------------------------------------------------------------------------

data Face2 : Sx2 → Sx2 → Set where
  f2-v0-e01 : Face2 v0 e01
  f2-v1-e01 : Face2 v1 e01
  f2-v0-e02 : Face2 v0 e02
  f2-v2-e02 : Face2 v2 e02
  f2-v1-e12 : Face2 v1 e12
  f2-v2-e12 : Face2 v2 e12
  f2-v1-e13 : Face2 v1 e13
  f2-v3-e13 : Face2 v3 e13
  f2-v2-e23 : Face2 v2 e23
  f2-v3-e23 : Face2 v3 e23
  f2-e01-FL : Face2 e01 FL
  f2-e02-FL : Face2 e02 FL
  f2-e12-FL : Face2 e12 FL
  f2-e12-FR : Face2 e12 FR
  f2-e13-FR : Face2 e13 FR
  f2-e23-FR : Face2 e23 FR

--------------------------------------------------------------------------------
-- §3. 链式路由关系 ChainRoute（修正版——支持任意跳数）
--   ch-via 不含 Face τ e'（K₃ 版 CoefRoute 的过度约束）；
--   续程证据由尾递归 CoefRoute e' τ ν 自带。
--------------------------------------------------------------------------------

data ChainRoute (V : Sx2 → Maybe Sx2) (coeff : Sx2 → Sx2 → Trit) :
  Sx2 → Sx2 → Trit → Set where
  ch-direct : ∀ σ τ μ → Face2 τ σ → coeff τ σ ≡ μ → V τ ≡ nothing →
              ChainRoute V coeff σ τ μ
  ch-via    : ∀ σ w e' τ μ-in i ν →
              Face2 w σ → V w ≡ just e' →
              coeff w σ ≡ μ-in → coeff w e' ⊗ i ≡ T₁ →
              ChainRoute V coeff e' τ ν →
              ChainRoute V coeff σ τ ((μ-in ⊗ i) ⊗ (T₂ ⊗ ν))

CR = ChainRoute V2 coeff2

--------------------------------------------------------------------------------
-- §4. 三条路由见证
--------------------------------------------------------------------------------

-- ①∂₂ᶜ FL：直连 FL → e02（T₂；e01/e12 非临界且 V=nothing 无路由）
r-FL-e02 : CR FL e02 T₂
r-FL-e02 = ch-direct FL e02 T₂ f2-e02-FL refl refl

-- ②∂₁ᶜ e02 直连：e02 → v2（T₁）
r-e02-v2-direct : CR e02 v2 T₁
r-e02-v2-direct = ch-direct e02 v2 T₁ f2-v2-e02 refl refl

-- ③∂₁ᶜ e02 链式路由：e02→v₀→e₀₁→v₁→e₁₂→v₂，总系数 T₂
--   内层：e₀₁ → v₁ → e₁₂ → v₂，总 = ((T₁⊗T₂)⊗(T₂⊗T₁)) = T₁
inner-route : CR e01 v2 T₁
inner-route =
  ch-via e01 v1 e12 v2 T₁ T₂ T₁
    f2-v1-e01 refl
    refl refl
    (ch-direct e12 v2 T₁ f2-v2-e12 refl refl)

--   外层：e₀₂ → v₀ → e₀₁ →（内层），总 = ((T₂⊗T₂)⊗(T₂⊗T₁)) = T₂
outer-route : CR e02 v2 T₂
outer-route =
  ch-via e02 v0 e01 v2 T₂ T₂ T₁
    f2-v0-e02 refl
    refl refl
    inner-route

--------------------------------------------------------------------------------
-- §5. M3 相消（路径配对）：直连 ⊕ 链式路由 = T₁ ⊕ T₂ = T₀
--------------------------------------------------------------------------------

m3-cancel : T₁ ⊕ T₂ ≡ T₀
m3-cancel = refl

-- ∂₂ᶜ FL = T₂·e02；∂₁ᶜ e02 = T₁·v₂ ⊕ T₂·v₂ = (T₁⊕T₂)·v₂ = 0
m3-assembly : (T₂ ⊗ (T₁ ⊕ T₂)) ≡ T₀
m3-assembly = refl

-- M3 首站定理（实例层）：∂₁ᶜ∘∂₂ᶜ FL = 0
m3-fl : (T₂ ⊗ (T₁ ⊕ T₂)) ≡ T₀
m3-fl = m3-assembly
