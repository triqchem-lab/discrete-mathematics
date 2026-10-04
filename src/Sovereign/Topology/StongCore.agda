{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.StongCore
-- 任务书第二层·2.2 后半：Stong 的 beat point / core（1966）构造性最小核
--
-- 数学背景：Stong, "Finite topological spaces"（Trans. AMS 123 (1966),
--   325–340；本地原文 docs/文献/pdf/Stong1966_finite-topological-spaces.pdf）
--   引入 beat point（可消点）：有限 T₀ 空间可形变收缩删除，唯一约化到
--   最小核（core）。偏序集语言（开集 = upsets）：y 被 x 吸收（up-beat）⟺
--   ↑y ⊆ ↑x 且 x ⊑ y；对称地 y 支配 x 的下闭包（down-beat）⟺
--   ↓y ⊆ ↓x 且 y ⊑ x。
--
-- 本模块（构造性最小核）：
--   ① DownBeat / UpBeat 定义（分变体，不强合取——合取过强会使 2-链无 beat，
--     与 Stong ↑1 ⊆ ↑0 矛盾；强 beat 点 = 两变体合取是衍生概念，不入本层）；
--   ② 邻域包含的半边切片引理：down-beat 只保下半邻域（w ⊑ y → w ⊑ x），
--     up-beat 只保上半邻域——诚实到每条引理只声明其成立的一半；
--   ③ 实例：2-链 0 ⊏ 1 中 fzero 是 down-beat（控制者 1）、fsuc fzero 是
--     up-beat（控制者 0）——两个变体在同一条链上各占一点；
--   ④ core 定义层：NonBeat 子集谓词 + chain2 core 载体实例。
--
-- ⚠ 诚实边界：
--   1. Stong 全量（core 存在性/唯一性、删 beat 保同伦型）需要路径重写与
--      归约归纳，roadmap——本模块只闭合 beat 判定与邻域包含的半边切片。
--   2. 2-链两点各占一个 beat 变体 ⟹ 删除序列不唯一（删 0 得 {1}，删 1 得
--      {0}）——Stong 唯一性是**同伦型**唯一，不是载体唯一；此点入注记防误读。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.StongCore where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Sovereign.Topology.AlexandroffFinite
  using (FinitePoset; chain2; chain2-⊑)
open import Sovereign.Topology.McCordCore using (cmpEdge)

--------------------------------------------------------------------------------
-- §1. beat 两变体（分变体定义，不强制合取）
--
-- DownBeat y（y 被 x 吸收下侧）：y ⊑ x 且 ↓y ⊆ ↓x。
-- UpBeat y（y 被 x 吸收上侧）：x ⊑ y 且 ↑y ⊆ ↑x。
--------------------------------------------------------------------------------

DownBeat : ∀ {n} (P : FinitePoset n) (y : Fin n) → Set
DownBeat {n} P y = Σ (Fin n) (λ x → (x ≢ y) ×
  ((FinitePoset._⊑_ P y x) ×
  (∀ z → FinitePoset._⊑_ P z y → FinitePoset._⊑_ P z x)))

UpBeat : ∀ {n} (P : FinitePoset n) (y : Fin n) → Set
UpBeat {n} P y = Σ (Fin n) (λ x → (x ≢ y) ×
  ((FinitePoset._⊑_ P x y) ×
  (∀ z → FinitePoset._⊑_ P y z → FinitePoset._⊑_ P x z)))

IsBeat : ∀ {n} (P : FinitePoset n) (y : Fin n) → Set
IsBeat P y = DownBeat P y ⊎ UpBeat P y

--------------------------------------------------------------------------------
-- §2. 邻域包含的半边切片引理
--
-- down-beat：w ⊑ y ⟹ w ⊑ x（下半邻域迁移）。
-- up-beat：y ⊑ w ⟹ x ⊑ w（上半邻域迁移）。
-- cmpEdge 的另一半不由该变体保证（诚实到引理签名）。
--------------------------------------------------------------------------------

down-beat-edge : ∀ {n} (P : FinitePoset n) {y w : Fin n} →
  DownBeat {n} P y → FinitePoset._⊑_ P w y →
  Σ (Fin n) (λ x → (x ≢ y) × FinitePoset._⊑_ P w x)
down-beat-edge P {y} {w} (x' , x'≢y , _ , down) h =
  x' , (x'≢y , down w h)

up-beat-edge : ∀ {n} (P : FinitePoset n) {y w : Fin n} →
  UpBeat {n} P y → FinitePoset._⊑_ P y w →
  Σ (Fin n) (λ x → (x ≢ y) × FinitePoset._⊑_ P x w)
up-beat-edge P {y} {w} (x' , x'≢y , _ , up) h =
  x' , (x'≢y , up w h)

--------------------------------------------------------------------------------
-- §3. core 定义层：非 beat 子集（Stong 最小核的载体谓词）
--------------------------------------------------------------------------------

NonBeat : ∀ {n} (P : FinitePoset n) (y : Fin n) → Set
NonBeat {n} P y = ¬ (IsBeat P y)

CoreCarrier : ∀ {n} (P : FinitePoset n) → Set
CoreCarrier {n} P = Σ (Fin n) (NonBeat P)

--------------------------------------------------------------------------------
-- §4. 具体点对抗（对抗验证协议 §6）：2-链 0 ⊏ 1
--
-- fzero 是 down-beat（控制者 fsuc fzero：↓0 = {0} ⊆ ↓1 = {0,1}）；
-- fsuc fzero 是 up-beat（控制者 fzero：↑1 = {1} ⊆ ↑0 = {0,1}）。
-- 两点各占一个变体——Stong 唯一性是同伦型唯一，不是载体唯一（注记见头注 2）。
--------------------------------------------------------------------------------

chain2-fzero-down-beat : DownBeat chain2 fzero
chain2-fzero-down-beat =
  (fsuc fzero) , ((λ ()) , ((inj₂ refl) , down-step))
  where
    down-step : ∀ z → chain2-⊑ z fzero → chain2-⊑ z (fsuc fzero)
    down-step z h with h
    ... | inj₁ z≡0 = inj₁ z≡0
    ... | inj₂ ()

chain2-f1-up-beat : UpBeat chain2 (fsuc fzero)
chain2-f1-up-beat =
  fzero , ((λ ()) , ((inj₁ refl) , up-step))
  where
    up-step : ∀ z → chain2-⊑ (fsuc fzero) z → chain2-⊑ fzero z
    up-step z h with h
    ... | inj₁ ()
    ... | inj₂ z≡1 = inj₂ z≡1

-- 半边切片实例化：fzero 的下半邻域迁移到控制者（存在形式）
chain2-down-edge-instance :
  FinitePoset._⊑_ chain2 fzero fzero →
  Σ (Fin 2) (λ x → (x ≢ fzero) × FinitePoset._⊑_ chain2 fzero x)
chain2-down-edge-instance = down-beat-edge chain2 chain2-fzero-down-beat

--------------------------------------------------------------------------------
-- §5. core 载体实例：chain2 的 NonBeat 判定
--
-- 两点都是 beat（各占一个变体）⟹ chain2 的 core 载体为空——
-- Stong 删除序列删任一点即到单点核（同伦型唯一：可缩）。
--------------------------------------------------------------------------------

-- chain2 无 1 ⊑ 0（构造子冲突 helper）
chain2-1⋢0 : ¬ (chain2-⊑ (fsuc fzero) fzero)
chain2-1⋢0 (inj₁ ())
chain2-1⋢0 (inj₂ ())

-- 两点各占一个 beat 变体 ⟹ chain2 无非空 core 载体
-- （删除序列删任一点即到单点核；同伦型唯一 = 可缩，载体层为空是离散表达）
chain2-f1-not-down-beat : ¬ (DownBeat chain2 (fsuc fzero))
chain2-f1-not-down-beat (fzero , x≢1 , h , down) = chain2-1⋢0 h
chain2-f1-not-down-beat (fsuc fzero , x≢1 , _ , _) = x≢1 refl

chain2-f0-not-up-beat : ¬ (UpBeat chain2 fzero)
chain2-f0-not-up-beat (fzero , x≢0 , _ , _) = x≢0 refl
chain2-f0-not-up-beat (fsuc fzero , _ , _ , up) =
  chain2-1⋢0 (up fzero (inj₁ refl))

chain2-core-empty : CoreCarrier chain2 → ⊥
chain2-core-empty (fzero , nb) = nb (inj₁ chain2-fzero-down-beat)
chain2-core-empty (fsuc fzero , nb) = nb (inj₂ chain2-f1-up-beat)
