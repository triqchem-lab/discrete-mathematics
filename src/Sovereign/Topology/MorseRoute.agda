{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseRoute
-- 任务书第五层·5.1 泛型化：交替路径路由的**关系形态**——
--   任意 f 的 Morse 边界路由的第一块泛型机件
--
-- 数学背景：代数 Morse 边界 ∂^crit 经**交替路径**（边界步 ↔ V-箭头）
--   路由。函数形态需要终止性论证（路径维度振荡不降）；本模块用
--   **归纳关系**形态规避终止性问题——关系无需递归终止。
--
--   核心定理（维度下降）：任何 MorseRoute σ τ 都有 dim τ < dim σ
--   ——路由严格降维，这是 Morse 复合边界算子良定义（只写入低维）
--   的结构根据，也是泛型 Morse 同调定理机件的第一块。
--
--   载体要求：MorseFieldG record（Face 面关系 + V 配对 + dim-law
--   + face-dim 严格降维——四字段）。
--
-- 复用：FormanMinimal.dim（降维目标）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseRoute where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)
open import Data.Nat.Properties using (<-trans; <-≤-trans; ≤-trans)

--------------------------------------------------------------------------------
-- §1. 泛型场 record（Face 面关系 + 严格降维律）
--------------------------------------------------------------------------------

record MorseFieldG (K : Set) (dimK : K → ℕ) : Set₁ where
  field
    Face     : K → K → Set                     -- Face τ σ：τ 是 σ 的面
    face-dim : ∀ τ σ → Face τ σ → dimK τ < dimK σ   -- 面严格降维
    V        : K → Maybe K                     -- 配对箭头
    dim-law  : ∀ σ τ → V σ ≡ just τ → dimK τ ≡ suc (dimK σ)

--------------------------------------------------------------------------------
-- §2. 交替路由关系（顶层归纳定义——规避函数递归终止性）
--
--   MorseRoute K V Face σ τ：σ 的 Morse 边界路由到 τ
--   r-direct：直连面项；r-via：经配对面 w（V w ↦ e'）路由继续
--------------------------------------------------------------------------------

data MorseRoute (K : Set) (V : K → Maybe K) (Face : K → K → Set) : K → K → Set where
  r-direct : ∀ σ τ → Face τ σ → MorseRoute K V Face σ τ
  r-via    : ∀ σ w e' τ →
             Face w σ → V w ≡ just e' → Face τ e' →
             MorseRoute K V Face e' τ →
             MorseRoute K V Face σ τ

--------------------------------------------------------------------------------
-- §3. 维度下降定理（泛型——归纳于路由推导）
--
--   r-direct 支：面降维直给。
--   r-via 支：dim τ < dim e'（面降维）∧ dim e' ≤ dim σ（配对升维
--     恰补齐面的降维：dim e' ≡ suc (dim w)，dim w < dim σ 的定义
--     展开即 suc (dim w) ≤ dim σ）⟹ dim τ < dim σ（<-≤-trans）。
--------------------------------------------------------------------------------

route-dim-descent : ∀ (K : Set) (dimK : K → ℕ)
                    (mf : MorseFieldG K dimK) →
                    ∀ σ τ → MorseRoute K (MorseFieldG.V mf)
                                (MorseFieldG.Face mf) σ τ →
                    dimK τ < dimK σ
route-dim-descent K dimK mf σ τ (r-direct .σ .τ hface) =
  MorseFieldG.face-dim mf τ σ hface
route-dim-descent K dimK mf σ τ
  (r-via .σ w e' .τ hface hw hface' hroute) =
    <-≤-trans τ<e' e'≤σ
  where
    open MorseFieldG mf

    -- dim w < dim σ（面降维）
    w<σ : dimK w < dimK σ
    w<σ = face-dim w σ hface

    -- dim e' ≡ suc (dim w)（配对升维）
    e'≡suc-w : dimK e' ≡ suc (dimK w)
    e'≡suc-w = dim-law w e' hw

    -- dim e' ≤ dim σ：suc (dim w) ≤ dim σ ← dim w < dim σ 的定义展开
    e'≤σ : dimK e' ≤ dimK σ
    e'≤σ = subst (λ z → z ≤ dimK σ) (sym e'≡suc-w) w<σ

    -- dim τ < dim e'（归纳假设作用于剩余路由 + 面降维）
    τ<e' : dimK τ < dimK e'
    τ<e' = face-dim τ e' hface'
