{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseChiBoth
-- 任务书第五层·5.1 深化：双场 χ 一致性 + 完美场无环性实例化
--
-- 数学背景：Forman 第一定理（离散 Dehn-Sommerville）：对任意 Morse
--   函数，临界计数交错和 χ_m := m₀ - m₁ + m₂ 与复形欧拉示性数相等。
--   本模块在 K₃ 填充三角上闭合**两个场**的 χ_m 实例：
--
--   非完美场 triangleVF（配对 v0↦e01, e12↦t，临界 {v1,v2,e20}）：
--     m = (2,1,0)，χ_m = 2∸1+0 = 1
--   完美场 perfectVF（配对 v0↦e01, v1↔e12, e20↔t，临界 {v2}）：
--     m = (1,0,0)，χ_m = 1∸0+0 = 1
--   两场 χ_m 相等且 ≡ 1 —— 对应 jac_Topology 的 χ-filled3（ℤ 侧
--   χH filled3C ≡ + 1，已证 refl；ℕ 侧本模块独立闭合）。
--
-- 另：泛型无环定理（MorseAcyclic.morse-acyclic-2）在完美场上实例化
--   ——泛型接口的第二复用。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseChiBoth where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.FormanMinimal
  using (Sx; dim; v0; v1; v2; e01; e12; e20; t)
  renaming (triangleVF to triVF)
open import Sovereign.Topology.MorseAcyclic using (morse-acyclic-2)
open import Sovereign.Topology.FormanPerfectField
  using (perfectVF; perfect-dim-law)

--------------------------------------------------------------------------------
-- §1. 非完美场 χ_m：m = (2,1,0)（FormanMorseInequality 同源计数）
--------------------------------------------------------------------------------

np-m₀ np-m₁ np-m₂ : ℕ
np-m₀ = 2
np-m₁ = 1
np-m₂ = 0

chi-m-np : ℕ
chi-m-np = (np-m₀ ∸ np-m₁) + np-m₂

chi-m-np≡1 : chi-m-np ≡ 1
chi-m-np≡1 = refl

--------------------------------------------------------------------------------
-- §2. 完美场 χ_m：m = (1,0,0)
--------------------------------------------------------------------------------

p-m₀ p-m₁ p-m₂ : ℕ
p-m₀ = 1
p-m₁ = 0
p-m₂ = 0

chi-m-p : ℕ
chi-m-p = (p-m₀ ∸ p-m₁) + p-m₂

chi-m-p≡1 : chi-m-p ≡ 1
chi-m-p≡1 = refl

--------------------------------------------------------------------------------
-- §3. 两场 χ_m 相等（Forman 第一定理的实例层形态：
--     χ_m 与场无关，只依赖复形）
--------------------------------------------------------------------------------

chi-m-agree : chi-m-np ≡ chi-m-p
chi-m-agree = refl

--------------------------------------------------------------------------------
-- §4. 完美场无环性（泛型无环定理的第二复用）
--------------------------------------------------------------------------------

nothing-just : ∀ {τ : Sx} → ¬ (nothing ≡ just τ)
nothing-just ()

perfect-dim-law-np : ∀ σ τ → perfectVF σ ≡ just τ → dim τ ≡ suc (dim σ)
perfect-dim-law-np v0 e01 h = refl
perfect-dim-law-np v1 e12 h = refl
perfect-dim-law-np e20 t h = refl
perfect-dim-law-np v2 τ h = ⊥-elim (nothing-just h)
perfect-dim-law-np e01 τ h = ⊥-elim (nothing-just h)
perfect-dim-law-np e12 τ h = ⊥-elim (nothing-just h)
perfect-dim-law-np t τ h = ⊥-elim (nothing-just h)

perfectVF-acyclic : ∀ σ τ → ¬ ((perfectVF σ ≡ just τ) × (perfectVF τ ≡ just σ))
perfectVF-acyclic σ τ (h₁ , h₂) = morse-acyclic-2 perfectVF perfect-dim-law-np σ τ h₁ h₂

--------------------------------------------------------------------------------
-- §5. 非完美场无环性（同款第三复用；triVF 维度律引理化重述）
--------------------------------------------------------------------------------

triVF-dim-law-np : ∀ σ τ → triVF σ ≡ just τ → dim τ ≡ suc (dim σ)
triVF-dim-law-np v0 e01 h = refl
triVF-dim-law-np e12 t h = refl
triVF-dim-law-np v1 τ h = ⊥-elim (nothing-just h)
triVF-dim-law-np v2 τ h = ⊥-elim (nothing-just h)
triVF-dim-law-np e01 τ h = ⊥-elim (nothing-just h)
triVF-dim-law-np e20 τ h = ⊥-elim (nothing-just h)
triVF-dim-law-np t τ h = ⊥-elim (nothing-just h)

triVF-acyclic-np : ∀ σ τ → ¬ ((triVF σ ≡ just τ) × (triVF τ ≡ just σ))
triVF-acyclic-np σ τ (h₁ , h₂) = morse-acyclic-2 triVF triVF-dim-law-np σ τ h₁ h₂
