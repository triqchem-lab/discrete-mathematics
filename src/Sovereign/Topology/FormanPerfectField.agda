{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.FormanPerfectField
-- 任务书第五层·5.1 深化：完美配对场的**形式合法性**
--
-- 数学背景：PerfectMorseInstance 闭合了完美临界计数（m = β = (1,0,0)），
--   但其配对表（v0↔e01, v1↔e12, e20↔t）以头注非形式给出。本模块把
--   配对合法性形式化：
--
--   ①FaceRel——三角形的 9 条直接面关系（data 显式枚举）
--   ②perfectVF——完美配对场（v0↦e01, v1↦e12, e20↦t，临界 {v2}）
--     作为 MorseField record（dim-law + 配对单射两条良构律全证；
--     单射经 just-dom 枚举组合——FormanMinimal V-just-dom 同款风格）
--   ③PairLegit——配对合法性 record（τ + 配对方程 + 面关系三件套）
--   ④v2 唯一临界：全 7 单形的 IsPaired/IsCritical 分类闭合
--
-- 技术要点：cubical 下矛盾消去全部经顶层构造子冲突助手（e01≢v2 等
--   λ ()，及 nothing-just）——零深分裂、零点模式依赖。
--
-- ⚠ 诚实边界：面关系为枚举 data（Sx 无顶点集结构，面表即语义）；
--   一般定理（完美 ⟺ 极小复形）roadmap。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.FormanPerfectField where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; subst)
open import Sovereign.Topology.FormanMinimal
  using (Sx; v0; v1; v2; e01; e12; e20; t; dim; MorseField)

--------------------------------------------------------------------------------
-- §0. 构造子冲突助手（顶层冲突，cubical 安全）
--------------------------------------------------------------------------------

v0≢v1 : ¬ (v0 ≡ v1)
v0≢v1 ()

v0≢e20 : ¬ (v0 ≡ e20)
v0≢e20 ()

v1≢e20 : ¬ (v1 ≡ e20)
v1≢e20 ()

e01≢e12 : ¬ (e01 ≡ e12)
e01≢e12 ()

e01≢t : ¬ (e01 ≡ t)
e01≢t ()

e12≢t : ¬ (e12 ≡ t)
e12≢t ()

e01≢v2 : ¬ (e01 ≡ v2)
e01≢v2 ()

e12≢v2 : ¬ (e12 ≡ v2)
e12≢v2 ()

t≢v2 : ¬ (e20 ≡ v2)
t≢v2 ()

tt≠v2 : ¬ (t ≡ v2)
tt≠v2 ()

nothing-just : ∀ {τ : Sx} → ¬ (nothing ≡ just τ)
nothing-just ()

--------------------------------------------------------------------------------
-- §1. 面关系：三角形的 9 条直接面关系（data 显式枚举）
--------------------------------------------------------------------------------

data FaceRel : Sx → Sx → Set where
  f-v0-e01 : FaceRel v0 e01
  f-v1-e01 : FaceRel v1 e01
  f-v1-e12 : FaceRel v1 e12
  f-v2-e12 : FaceRel v2 e12
  f-v0-e20 : FaceRel v0 e20
  f-v2-e20 : FaceRel v2 e20
  f-e01-t  : FaceRel e01 t
  f-e12-t  : FaceRel e12 t
  f-e20-t  : FaceRel e20 t

--------------------------------------------------------------------------------
-- §2. 完美配对场
--------------------------------------------------------------------------------

perfectVF : Sx → Maybe Sx
perfectVF v0  = just e01
perfectVF v1  = just e12
perfectVF v2  = nothing
perfectVF e01 = nothing
perfectVF e12 = nothing
perfectVF e20 = just t
perfectVF t   = nothing

-- dim 数值锚（复用 FormanMinimal.dim，refl 计算闭合）
dim-v0 : dim v0 ≡ 0
dim-v0 = refl

dim-e01 : dim e01 ≡ 1
dim-e01 = refl

dim-v1 : dim v1 ≡ 0
dim-v1 = refl

dim-e12 : dim e12 ≡ 1
dim-e12 = refl

dim-e20 : dim e20 ≡ 1
dim-e20 = refl

dim-t : dim t ≡ 2
dim-t = refl

--------------------------------------------------------------------------------
-- §3. 良构律一：维度律（τ 恰高一维；点模式经 h=refl 强制 τ）
--------------------------------------------------------------------------------

perfect-dim-law : ∀ σ τ → perfectVF σ ≡ just τ → dim τ ≡ suc (dim σ)
perfect-dim-law v0 .e01 refl = refl
perfect-dim-law v1 .e12 refl = refl
perfect-dim-law v2 τ h = ⊥-elim (nothing-just h)
perfect-dim-law e01 τ h = ⊥-elim (nothing-just h)
perfect-dim-law e12 τ h = ⊥-elim (nothing-just h)
perfect-dim-law e20 .t refl = refl
perfect-dim-law t τ h = ⊥-elim (nothing-just h)

--------------------------------------------------------------------------------
-- §4. 良构律二：配对单射（just-dom 枚举组合）
--------------------------------------------------------------------------------

perfectV-just-dom : ∀ σ s → perfectVF σ ≡ just s → σ ≡ v0 ⊎ σ ≡ v1 ⊎ σ ≡ e20
perfectV-just-dom v0 s h = inj₁ refl
perfectV-just-dom v1 s h = inj₂ (inj₁ refl)
perfectV-just-dom v2 s ()
perfectV-just-dom e01 s ()
perfectV-just-dom e12 s ()
perfectV-just-dom e20 s h = inj₂ (inj₂ refl)
perfectV-just-dom t s ()

τ≡e01 : ∀ {τ} → perfectVF v0 ≡ just τ → e01 ≡ τ
τ≡e01 h = just-injective h

τ≡e12 : ∀ {τ} → perfectVF v1 ≡ just τ → e12 ≡ τ
τ≡e12 h = just-injective h

τ≡t : ∀ {τ} → perfectVF e20 ≡ just τ → t ≡ τ
τ≡t h = just-injective h

perfect-V-inj : ∀ σ σ' τ → perfectVF σ ≡ just τ → perfectVF σ' ≡ just τ → σ ≡ σ'
perfect-V-inj σ σ' τ h₁ h₂
  with perfectV-just-dom σ τ h₁ | perfectV-just-dom σ' τ h₂
... | inj₁ hσ | inj₁ hσ' = trans hσ (sym hσ')
... | inj₁ hσ | inj₂ (inj₁ hσ') =
    ⊥-elim (e01≢e12 (trans (τ≡e01 (subst (λ w → perfectVF w ≡ just τ) hσ h₁)) (sym (τ≡e12 (subst (λ w → perfectVF w ≡ just τ) hσ' h₂)))))
... | inj₁ hσ | inj₂ (inj₂ hσ') =
    ⊥-elim (e01≢t (trans (τ≡e01 (subst (λ w → perfectVF w ≡ just τ) hσ h₁)) (sym (τ≡t (subst (λ w → perfectVF w ≡ just τ) hσ' h₂)))))
... | inj₂ (inj₁ hσ) | inj₁ hσ' =
    ⊥-elim (e01≢e12 (trans (τ≡e01 (subst (λ w → perfectVF w ≡ just τ) hσ' h₂)) (sym (τ≡e12 (subst (λ w → perfectVF w ≡ just τ) hσ h₁)))))
... | inj₂ (inj₁ hσ) | inj₂ (inj₁ hσ') = trans hσ (sym hσ')
... | inj₂ (inj₁ hσ) | inj₂ (inj₂ hσ') =
    ⊥-elim (e12≢t (trans (τ≡e12 (subst (λ w → perfectVF w ≡ just τ) hσ h₁)) (sym (τ≡t (subst (λ w → perfectVF w ≡ just τ) hσ' h₂)))))
... | inj₂ (inj₂ hσ) | inj₁ hσ' =
    ⊥-elim (e01≢t (trans (τ≡e01 (subst (λ w → perfectVF w ≡ just τ) hσ' h₂)) (sym (τ≡t (subst (λ w → perfectVF w ≡ just τ) hσ h₁)))))
... | inj₂ (inj₂ hσ) | inj₂ (inj₁ hσ') =
    ⊥-elim (e12≢t (trans (τ≡e12 (subst (λ w → perfectVF w ≡ just τ) hσ' h₂)) (sym (τ≡t (subst (λ w → perfectVF w ≡ just τ) hσ h₁)))))
... | inj₂ (inj₂ hσ) | inj₂ (inj₂ hσ') = trans hσ (sym hσ')

perfect-field : MorseField
perfect-field = record
  { V       = perfectVF
  ; dim-law = perfect-dim-law
  ; V-inj   = perfect-V-inj
  }

--------------------------------------------------------------------------------
-- §5. 配对合法性：record 封装（τ + 配对方程 + 面关系，零模式匹配）
--------------------------------------------------------------------------------

record PairLegit (σ : Sx) : Set where
  constructor pair-legit
  field
    τ        : Sx
    h        : perfectVF σ ≡ just τ
    faceful  : FaceRel σ τ

-- 三支配对合法性（配对箭头保持面关系——Forman 配对第一合法性）
legit-v0 : PairLegit v0
legit-v0 = pair-legit e01 refl f-v0-e01

legit-v1 : PairLegit v1
legit-v1 = pair-legit e12 refl f-v1-e12

legit-e20 : PairLegit e20
legit-e20 = pair-legit t refl f-e20-t

--------------------------------------------------------------------------------
-- §6. 临界分类：v2 唯一临界（全 7 单形闭合）
--------------------------------------------------------------------------------

IsPairedP : Sx → Set
IsPairedP σ =
  (∃ (λ τ → perfectVF σ ≡ just τ))
  ⊎ (∃ (λ τ → perfectVF τ ≡ just σ))

IsCriticalP : Sx → Set
IsCriticalP σ = ¬ IsPairedP σ

-- v2 唯一临界
v2-critical : IsCriticalP v2
v2-critical (inj₁ (τ , h)) = ⊥-elim (nothing-just h)
v2-critical (inj₂ (τ , h)) = ⊥-elim (aux τ h)
  where
    aux : ∀ τ → perfectVF τ ≡ just v2 → ⊥
    aux v0 h = ⊥-elim (e01≢v2 (just-injective h))
    aux v1 h = ⊥-elim (e12≢v2 (just-injective h))
    aux v2 h = ⊥-elim (nothing-just h)
    aux e01 h = ⊥-elim (nothing-just h)
    aux e12 h = ⊥-elim (nothing-just h)
    aux e20 h = ⊥-elim (tt≠v2 (just-injective h))
    aux t h = ⊥-elim (nothing-just h)

-- 其余 6 单形全部配对
v0-paired : IsPairedP v0
v0-paired = inj₁ (e01 , refl)

v1-paired : IsPairedP v1
v1-paired = inj₁ (e12 , refl)

e01-paired : IsPairedP e01
e01-paired = inj₂ (v0 , refl)

e12-paired : IsPairedP e12
e12-paired = inj₂ (v1 , refl)

e20-paired : IsPairedP e20
e20-paired = inj₁ (t , refl)

t-paired : IsPairedP t
t-paired = inj₂ (e20 , refl)
