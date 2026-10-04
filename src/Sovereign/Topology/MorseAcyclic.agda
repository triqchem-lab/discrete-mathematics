{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseAcyclic
-- 任务书第五层·5.1 补件：Morse 配对场的**无环性**（泛型）
--
-- 数学背景：Forman 配对箭头 σ → τ（V σ ≡ just τ）满足维度律
--   dim τ = suc (dim σ)——箭头严格升维。因此配对箭头**不可能出现
--   有向环**：2-环（σ→τ→σ）立即矛盾（dim τ ≡ suc (dim σ) ≡ suc
--   (dim τ) 给 n ≡ suc n）。这是梯度型矢量场无环性的离散代数核心。
--
-- 本模块给出泛型无环定理（取 V 与 dim-law 为参数）+ FormanMinimal
--   triangleVF 的实例化。
--
-- 复用：FormanMinimal.Sx/triangleVF/dim（Topology/ 目录 Morse 分类）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseAcyclic where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)
open import Data.Nat.Properties using (suc-injective)
open import Sovereign.Topology.FormanMinimal
  using (Sx; dim; MorseField)

--------------------------------------------------------------------------------
-- §1. 泛型引理：n ≢ suc n
--------------------------------------------------------------------------------

n≢suc2 : ∀ (n : ℕ) → ¬ (n ≡ suc (suc n))
n≢suc2 zero ()
n≢suc2 (suc m) h = n≢suc2 m (suc-injective h)

--------------------------------------------------------------------------------
-- §2. 泛型无环定理：维度律严格升维 ⟹ 无 2-环
--
--   取任意 V : Sx → Maybe Sx 及其维度律（MorseField.dim-law 形状），
--   则不存在 σ τ 使 V σ ≡ just τ 且 V τ ≡ just σ。
--------------------------------------------------------------------------------

morse-acyclic-2 : (V : Sx → Maybe Sx) →
                  (∀ σ τ → V σ ≡ just τ → dim τ ≡ suc (dim σ)) →
                  ∀ σ τ → V σ ≡ just τ → V τ ≡ just σ → ⊥
morse-acyclic-2 V dl σ τ h₁ h₂ =
  ⊥-elim (n≢suc2 (dim τ) (trans dl₁ (cong suc dl₂)))
  where
    dl₁ : dim τ ≡ suc (dim σ)
    dl₁ = dl σ τ h₁
    dl₂ : dim σ ≡ suc (dim τ)
    dl₂ = dl τ σ h₂

--------------------------------------------------------------------------------
-- §3. 实例：FormanMinimal triangleVF（配对 v0↦e01, e12↦t）无环
--------------------------------------------------------------------------------

open import Data.Maybe using (Maybe; just)
open import Sovereign.Topology.FormanMinimal renaming (triangleVF to triVF)

nothing-just : ∀ {τ : Sx} → ¬ (nothing ≡ just τ)
nothing-just ()

triVF-dim-law : ∀ σ τ → triVF σ ≡ just τ → dim τ ≡ suc (dim σ)
triVF-dim-law v0 e01 h = refl
triVF-dim-law v1 e12 h = refl
triVF-dim-law e12 t h = refl
triVF-dim-law v2 τ h = ⊥-elim (nothing-just h)
triVF-dim-law e01 τ h = ⊥-elim (nothing-just h)
triVF-dim-law e20 τ h = ⊥-elim (nothing-just h)
triVF-dim-law t τ h = ⊥-elim (nothing-just h)

triangleVF-acyclic : ∀ σ τ → ¬ ((triVF σ ≡ just τ) × (triVF τ ≡ just σ))
triangleVF-acyclic σ τ (h₁ , h₂) = morse-acyclic-2 triVF triVF-dim-law σ τ h₁ h₂
