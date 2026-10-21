{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Analysis.DiscreteODESolvable

module Sovereign.Synthesis.Analysis.DiscreteODESolvable where

open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.Analytic.ProjectionDifferential using (GF3Func; Δ; sum3)

--------------------------------------------------------------------------------
-- §3. ★★ 离散 Fredholm 替代：`Δu = v` **可解 ⟺ `sum3 v ≡ T₀`**
--
-- 必要性（`sum3 (Δ f) ≡ T₀`）是望远镜求和；充分性由「取常数为 0 的积分」给出：
--   `f = (T₀ , v₀ , v₀ ⊕ v₁)` ⇒ `Δ f = (v₀ , v₁ , ⊖(v₀⊕v₁)) = (v₀,v₁,v₂)`（用 `sum3 v ≡ T₀`）。
-- 27 情形穷举（9 个满足 `sum3 v ≡ T₀` 的真的给见证，其余 18 个由 `()` 排除）。
--------------------------------------------------------------------------------

Δ-solvable : ∀ v → sum3 v ≡ T₀ → Σ GF3Func (λ f → Δ f ≡ v)
Δ-solvable (T₀ , T₀ , T₀) refl = (T₀ , T₀ , T₀ ⊕ T₀) , refl
Δ-solvable (T₀ , T₀ , T₁) ()
Δ-solvable (T₀ , T₀ , T₂) ()
Δ-solvable (T₀ , T₁ , T₀) ()
Δ-solvable (T₀ , T₁ , T₁) ()
Δ-solvable (T₀ , T₁ , T₂) refl = (T₀ , T₀ , T₀ ⊕ T₁) , refl
Δ-solvable (T₀ , T₂ , T₀) ()
Δ-solvable (T₀ , T₂ , T₁) refl = (T₀ , T₀ , T₀ ⊕ T₂) , refl
Δ-solvable (T₀ , T₂ , T₂) ()
Δ-solvable (T₁ , T₀ , T₀) ()
Δ-solvable (T₁ , T₀ , T₁) ()
Δ-solvable (T₁ , T₀ , T₂) refl = (T₀ , T₁ , T₁ ⊕ T₀) , refl
Δ-solvable (T₁ , T₁ , T₀) ()
Δ-solvable (T₁ , T₁ , T₁) refl = (T₀ , T₁ , T₁ ⊕ T₁) , refl
Δ-solvable (T₁ , T₁ , T₂) ()
Δ-solvable (T₁ , T₂ , T₀) refl = (T₀ , T₁ , T₁ ⊕ T₂) , refl
Δ-solvable (T₁ , T₂ , T₁) ()
Δ-solvable (T₁ , T₂ , T₂) ()
Δ-solvable (T₂ , T₀ , T₀) ()
Δ-solvable (T₂ , T₀ , T₁) refl = (T₀ , T₂ , T₂ ⊕ T₀) , refl
Δ-solvable (T₂ , T₀ , T₂) ()
Δ-solvable (T₂ , T₁ , T₀) refl = (T₀ , T₂ , T₂ ⊕ T₁) , refl
Δ-solvable (T₂ , T₁ , T₁) ()
Δ-solvable (T₂ , T₁ , T₂) ()
Δ-solvable (T₂ , T₂ , T₀) ()
Δ-solvable (T₂ , T₂ , T₁) ()
Δ-solvable (T₂ , T₂ , T₂) refl = (T₀ , T₂ , T₂ ⊕ T₂) , refl

--------------------------------------------------------------------------------
-- §4. 必要性：`Δ` 的像落在「和为 0」的子空间里（望远镜求和）
--------------------------------------------------------------------------------

sum3-Δ : ∀ f → sum3 (Δ f) ≡ T₀
sum3-Δ (T₀ , T₀ , T₀) = refl
sum3-Δ (T₀ , T₀ , T₁) = refl
sum3-Δ (T₀ , T₀ , T₂) = refl
sum3-Δ (T₀ , T₁ , T₀) = refl
sum3-Δ (T₀ , T₁ , T₁) = refl
sum3-Δ (T₀ , T₁ , T₂) = refl
sum3-Δ (T₀ , T₂ , T₀) = refl
sum3-Δ (T₀ , T₂ , T₁) = refl
sum3-Δ (T₀ , T₂ , T₂) = refl
sum3-Δ (T₁ , T₀ , T₀) = refl
sum3-Δ (T₁ , T₀ , T₁) = refl
sum3-Δ (T₁ , T₀ , T₂) = refl
sum3-Δ (T₁ , T₁ , T₀) = refl
sum3-Δ (T₁ , T₁ , T₁) = refl
sum3-Δ (T₁ , T₁ , T₂) = refl
sum3-Δ (T₁ , T₂ , T₀) = refl
sum3-Δ (T₁ , T₂ , T₁) = refl
sum3-Δ (T₁ , T₂ , T₂) = refl
sum3-Δ (T₂ , T₀ , T₀) = refl
sum3-Δ (T₂ , T₀ , T₁) = refl
sum3-Δ (T₂ , T₀ , T₂) = refl
sum3-Δ (T₂ , T₁ , T₀) = refl
sum3-Δ (T₂ , T₁ , T₁) = refl
sum3-Δ (T₂ , T₁ , T₂) = refl
sum3-Δ (T₂ , T₂ , T₀) = refl
sum3-Δ (T₂ , T₂ , T₁) = refl
sum3-Δ (T₂ , T₂ , T₂) = refl
