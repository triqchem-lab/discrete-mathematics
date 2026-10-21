{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Analysis.DiscreteODESolvable

module Sovereign.Synthesis.Analysis.DiscreteODESolvable where

open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.Analytic.ProjectionDifferential using (GF3Func; Δ; sum3; Δ²-is-const)

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

--------------------------------------------------------------------------------
-- §5. ★★ H¹ = 0（闭 = 恰当）：离散 de Rham 第 1 上同调为零
--
-- 库内 `Δ²-is-const : Δ (Δ f) ≡ (sum3 f , sum3 f , sum3 f)` ⇒
--   `Δ² v ≡ 0  ⟺  sum3 v ≡ T₀  ⟺  v 落在 Δ 的像里`（最后一步是 §3 的 `Δ-solvable`）。
-- ⇒ 「闭形式 = 恰当形式」：**第 1 上同调群为 0**，与 `DiscreteODE.Δ-kernel-const`
--   （H⁰ = 常数）合起来给出完整的（两项）上同调。
--------------------------------------------------------------------------------

zero3 : GF3Func
zero3 = T₀ , T₀ , T₀

-- `(s , s , s) ≡ 0 ⇒ s ≡ T₀`（三情形）
const-zero : ∀ s → (s , s , s) ≡ zero3 → s ≡ T₀
const-zero T₀ e = refl
const-zero T₁ ()
const-zero T₂ ()

-- 闭形式 ⇒ 全和为 0
closed-sum-zero : ∀ v → Δ (Δ v) ≡ zero3 → sum3 v ≡ T₀
closed-sum-zero v e with v
... | (a , b , c) = const-zero (sum3 (a , b , c)) (trans (sym (Δ²-is-const (a , b , c))) e)

-- ★ H¹ = 0：闭形式必恰当（必是某个 f 的 Δ）
h1-vanishes : ∀ v → Δ (Δ v) ≡ zero3 → Σ GF3Func (λ f → Δ f ≡ Δ v)
h1-vanishes v e = Δ-solvable (Δ v) (sum3-Δ v)
