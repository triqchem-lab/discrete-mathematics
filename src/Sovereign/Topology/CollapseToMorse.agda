{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.CollapseToMorse
-- 任务书第五层·5.1 推进：可坍缩 ⟹ 完美 Morse（B4 正向实例）
--
-- 数学背景：坍缩序列 (e01,t) → (v1,e12) → (v2,e20)（Collapse.agda）
--   诱导 Morse 场 collapseVF：每个坍缩对 (τ,σ) 给出配对 τ↔σ：
--     collapseVF v1 = e12、v2 = e20、e01 = t，临界 = {v0}
--   m = (1,0,0) = β —— **完美**。
--
-- 【实例证据】K₃ 上存在**两个不同**的完美场：
--     perfectVF（v0↔e01, v1↔e12, e20↔t，临界 {v2}）
--     collapseVF（v1↔e12, v2↔e20, e01↔t，临界 {v0}）
--   完美 Morse 函数**非唯一**——两者临界单形集不同（{v2} vs {v0}）
--   但计数同为 (1,0,0)。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.CollapseToMorse where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.FormanMinimal
  using (Sx; dim; v0; v1; v2; e01; e12; e20; t; MorseField)
open import Sovereign.Topology.FormanPerfectField
  using (perfectVF; nothing-just; e12≢t; e01≢v2)

--------------------------------------------------------------------------------
-- §1. 构造子冲突助手
--------------------------------------------------------------------------------

e20≢e12 : ¬ (e20 ≡ e12)
e20≢e12 ()

t≢e12 : ¬ (t ≡ e12)
t≢e12 ()

e12≢e20 : ¬ (e12 ≡ e20)
e12≢e20 ()

e20≢t : ¬ (e20 ≡ t)
e20≢t ()

t≢e20 : ¬ (t ≡ e20)
t≢e20 ()

e12≢v0 : ¬ (e12 ≡ v0)
e12≢v0 ()

t≢v0 : ¬ (t ≡ v0)
t≢v0 ()

e12≢e01 : ¬ (e12 ≡ e01)
e12≢e01 ()

e20≢e01 : ¬ (e20 ≡ e01)
e20≢e01 ()

t≢e01 : ¬ (t ≡ e01)
t≢e01 ()

--------------------------------------------------------------------------------
-- §2. 坍缩诱导 Morse 场
--------------------------------------------------------------------------------

collapseVF : Sx → Maybe Sx
collapseVF v0  = nothing
collapseVF v1  = just e12
collapseVF v2  = just e20
collapseVF e01 = just t
collapseVF e12 = nothing
collapseVF e20 = nothing
collapseVF t   = nothing

--------------------------------------------------------------------------------
-- §3. 良构律一：维度律（零点模式，合法支具体 τ）
--------------------------------------------------------------------------------

collapse-dim-law : ∀ σ τ → collapseVF σ ≡ just τ → dim τ ≡ suc (dim σ)
collapse-dim-law v1 .e12 refl = refl
collapse-dim-law v2 .e20 refl = refl
collapse-dim-law e01 .t refl = refl
collapse-dim-law v0 τ h = ⊥-elim (nothing-just h)
collapse-dim-law e12 τ h = ⊥-elim (nothing-just h)
collapse-dim-law e20 τ h = ⊥-elim (nothing-just h)
collapse-dim-law t τ h = ⊥-elim (nothing-just h)

--------------------------------------------------------------------------------
-- §4. 良构律二：配对单射（零点模式 28 分支）
--------------------------------------------------------------------------------

collapse-V-inj : ∀ σ σ' τ → collapseVF σ ≡ just τ → collapseVF σ' ≡ just τ → σ ≡ σ'
collapse-V-inj v1 v1 e12 h₁ h₂ = refl
collapse-V-inj v2 v2 e20 h₁ h₂ = refl
collapse-V-inj e01 e01 t h₁ h₂ = refl
collapse-V-inj v0 σ' τ h₁ h₂ = ⊥-elim (nothing-just h₁)
collapse-V-inj e12 σ' τ h₁ h₂ = ⊥-elim (nothing-just h₁)
collapse-V-inj e20 σ' τ h₁ h₂ = ⊥-elim (nothing-just h₁)
collapse-V-inj t σ' τ h₁ h₂ = ⊥-elim (nothing-just h₁)
collapse-V-inj v1 v0 e12 h₁ h₂ = ⊥-elim (nothing-just h₂)
collapse-V-inj v1 e12 e12 h₁ h₂ = ⊥-elim (nothing-just h₂)
collapse-V-inj v1 e20 e12 h₁ h₂ = ⊥-elim (nothing-just h₂)
collapse-V-inj v1 t e12 h₁ h₂ = ⊥-elim (nothing-just h₂)
collapse-V-inj v2 v0 e20 h₁ h₂ = ⊥-elim (nothing-just h₂)
collapse-V-inj v2 v1 e20 h₁ h₂ = ⊥-elim (e12≢e20 (just-injective h₂))
collapse-V-inj v2 e01 e20 h₁ h₂ = ⊥-elim (t≢e20 (just-injective h₂))
collapse-V-inj v2 e12 e20 h₁ h₂ = ⊥-elim (nothing-just h₂)
collapse-V-inj v2 t e20 h₁ h₂ = ⊥-elim (nothing-just h₂)
collapse-V-inj e01 v0 t h₁ h₂ = ⊥-elim (nothing-just h₂)
collapse-V-inj e01 v1 t h₁ h₂ = ⊥-elim (e12≢t (just-injective h₂))
collapse-V-inj e01 v2 t h₁ h₂ = ⊥-elim (e20≢t (just-injective h₂))
collapse-V-inj e01 e12 t h₁ h₂ = ⊥-elim (nothing-just h₂)
collapse-V-inj e01 e20 t h₁ h₂ = ⊥-elim (nothing-just h₂)
collapse-V-inj e01 t t h₁ h₂ = ⊥-elim (nothing-just h₂)

collapse-field : MorseField
collapse-field = record
  { V       = collapseVF
  ; dim-law = collapse-dim-law
  ; V-inj   = collapse-V-inj
  }

--------------------------------------------------------------------------------
-- §5. 完美性：临界 = {v0}（m = (1,0,0)）
--------------------------------------------------------------------------------

IsCriticalC : Sx → Set
IsCriticalC σ = (collapseVF σ ≡ nothing) × (∀ τ → ¬ (collapseVF τ ≡ just σ))

-- e20≢v2 助手（顶层冲突）
e20≢v2 : ¬ (e20 ≡ v2)
e20≢v2 ()

e20≢v0 : ¬ (e20 ≡ v0)
e20≢v0 ()

v0-critical : IsCriticalC v0
v0-critical = (refl , nf)
  where
    nf : ∀ τ → ¬ (collapseVF τ ≡ just v0)
    nf v1 h = ⊥-elim (e12≢v0 (just-injective h))
    nf v2 h = ⊥-elim (e20≢v0 (just-injective h))
    nf e01 h = ⊥-elim (t≢v0 (just-injective h))
    nf v0 h = ⊥-elim (nothing-just h)
    nf e12 h = ⊥-elim (nothing-just h)
    nf e20 h = ⊥-elim (nothing-just h)
    nf t h = ⊥-elim (nothing-just h)

-- 其余单形全部配对（m₁ 计数为零的根据）
v1-paired : collapseVF v1 ≡ just e12
v1-paired = refl

v2-paired : collapseVF v2 ≡ just e20
v2-paired = refl

e01-paired : collapseVF e01 ≡ just t
e01-paired = refl
