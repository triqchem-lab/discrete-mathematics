{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.FreeAbHomology
-- 任务书第二层·2.5 推进：FreeAb 载体上的同调消没实例（H₁ = 0）
--
-- 数学背景：K₃ 填充三角（FreeAbBoundary 的链群 C₂--∂₂-->C₁--∂₁-->C₀）
--   的第一同调：Z₁ = ker ∂₁，本模块证明**循环刻画定理**——
--     任意闭链 x（∂₁ x ≡ 0 逐点）的三个边系数全部相等：
--       x 0 ≡ x 1 ≡ x 2 =: c
--   即 Z₁ = { c·(1,1,1) : c ∈ GF(3) } = im ∂₂（∂₂ 把系数 c 逐位复制）——
--   **H₁ = Z₁/B₁ = 0**（逐点意义）。
--
--   代数根基：GF(3) 消去律 a + 2b ≡ 0 → a ≡ b（9 case 枚举，
--   3 支 refl + 6 支构造子冲突 λ ()——cubical 单层安全）。
--
--   与 EckmannNonSplitting 的关系：恰因 H₁ = 0 且 GF(3) 上 ∂₂ 的像
--   不可补（non-splitting witness），Eckmann 直和分解失效——本模块
--   是那个现象的**算术侧根基**。
--
-- 复用：FreeAb（载体）、FreeAbBoundary（∂₁/∂₂）、Base/Trit（算术）。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.FreeAbHomology where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.FreeAb using (FAb)
open import Sovereign.Problem.Hodge.FreeAbBoundary using (∂₁; ∂₂; C₁)

--------------------------------------------------------------------------------
-- §1. GF(3) 消去律：a + 2b ≡ 0 → a ≡ b（9 case；6 支构造子冲突 λ ()）
--------------------------------------------------------------------------------

cancel-2 : ∀ (a b : Trit) → (a ⊕ (b ⊗ T₂)) ≡ T₀ → a ≡ b
cancel-2 T₀ T₀ h = refl
cancel-2 T₀ T₁ ()
cancel-2 T₀ T₂ ()
cancel-2 T₁ T₀ ()
cancel-2 T₁ T₁ h = refl
cancel-2 T₁ T₂ ()
cancel-2 T₂ T₀ ()
cancel-2 T₂ T₁ ()
cancel-2 T₂ T₂ h = refl

--------------------------------------------------------------------------------
-- §2. 循环刻画定理：闭链的边系数全相等
--
--   ∂₁ x = 0 逐点给两个方程：
--     v₁: x₀ + 2x₁ ≡ 0 → x₀ ≡ x₁（cancel-2）
--     v₂: x₁ + 2x₂ ≡ 0 → x₁ ≡ x₂（cancel-2）
--------------------------------------------------------------------------------

cycle-coeffs-equal : ∀ (x : C₁) → (∀ i → ∂₁ x i ≡ T₀) →
                     (x fzero ≡ x (fsuc fzero)) ×
                     (x (fsuc fzero) ≡ x (fsuc (fsuc fzero)))
cycle-coeffs-equal x h =
  cancel-2 (x fzero) (x (fsuc fzero)) (h (fsuc fzero)) ,
  cancel-2 (x (fsuc fzero)) (x (fsuc (fsuc fzero))) (h (fsuc (fsuc fzero)))

--------------------------------------------------------------------------------
-- §3. H₁ = 0（逐点）：Z₁ = im ∂₂
--
--   任意闭链 x 逐点等于 ∂₂(λ _ → x fzero)（系数 c := x fzero 的复制）。
--------------------------------------------------------------------------------

z₁-is-im-∂₂ : ∀ (x : C₁) → (∀ i → ∂₁ x i ≡ T₀) →
              ∀ (i : Fin 3) → x i ≡ ∂₂ (λ _ → x fzero) i
z₁-is-im-∂₂ x h i with cycle-coeffs-equal x h
... | (e₀₁ , e₁₂) = pointwise x i e₀₁ e₁₂
  where
    pointwise : ∀ (x : C₁) (i : Fin 3) →
                x fzero ≡ x (fsuc fzero) →
                x (fsuc fzero) ≡ x (fsuc (fsuc fzero)) →
                x i ≡ ∂₂ (λ _ → x fzero) i
    pointwise x fzero e₀₁ e₁₂ = refl
    pointwise x (fsuc fzero) e₀₁ e₁₂ = sym e₀₁
    pointwise x (fsuc (fsuc fzero)) e₀₁ e₁₂ = sym (trans e₀₁ e₁₂)

--------------------------------------------------------------------------------
-- §4. 消没推论：循环差的约束（c 相同则差为零的逐点预览）
--------------------------------------------------------------------------------

-- 循环 x 的三系数互差：任意两分量相等（刻画定理的 3×3 展开版）
cycle-diff-zero : ∀ (x : C₁) → (∀ i → ∂₁ x i ≡ T₀) →
                  ∀ (i j : Fin 3) → x i ≡ x j
cycle-diff-zero x h i j with cycle-coeffs-equal x h
... | (e₀₁ , e₁₂) = all-equal x i j e₀₁ e₁₂
  where
    all-equal : ∀ (x : C₁) (i j : Fin 3) →
                x fzero ≡ x (fsuc fzero) →
                x (fsuc fzero) ≡ x (fsuc (fsuc fzero)) →
                x i ≡ x j
    all-equal x fzero fzero e₀₁ e₁₂ = refl
    all-equal x fzero (fsuc fzero) e₀₁ e₁₂ = e₀₁
    all-equal x fzero (fsuc (fsuc fzero)) e₀₁ e₁₂ = trans e₀₁ e₁₂
    all-equal x (fsuc fzero) fzero e₀₁ e₁₂ = sym e₀₁
    all-equal x (fsuc fzero) (fsuc fzero) e₀₁ e₁₂ = refl
    all-equal x (fsuc fzero) (fsuc (fsuc fzero)) e₀₁ e₁₂ = e₁₂
    all-equal x (fsuc (fsuc fzero)) fzero e₀₁ e₁₂ = sym (trans e₀₁ e₁₂)
    all-equal x (fsuc (fsuc fzero)) (fsuc fzero) e₀₁ e₁₂ = sym e₁₂
    all-equal x (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) e₀₁ e₁₂ = refl
