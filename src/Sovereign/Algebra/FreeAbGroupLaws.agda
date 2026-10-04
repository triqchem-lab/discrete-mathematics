{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.FreeAbGroupLaws
-- 任务书第二层·2.5 泛型化（GAP-M7a-fab-laws）：FAb 群律补全 + ∂₁ 线性三条
--
-- 数学背景：GAP-M7a-im-equiv（Σ 商等价 isEquivRel）的前置——im-∂ 的
--   子群性完全归约为 ∂ 的线性性三条（∂-add/∂-neg/∂-zero）；FAb 的
--   群律（x+ᶠnegᶠx ≡ zeroᶠ 等）是商等价 refl 义务的前置。
--
--   三检查结论落地：FAb = 交换群（逐点律形态，negᶠ 在库）；
--   ∂ 线性性三条全缺（本模块补齐，K₃ ∂₁ 字面量表逐点 + ac4 重排）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.FreeAbGroupLaws where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
         ⊕-assoc; ⊕-comm; ⊕-identityˡ; ⊕-identityʳ;
         ⊗-assoc; ⊗-comm; ⊗-identityʳ; ⊗-distribˡ-⊕)
open import Sovereign.Algebra.FreeAb
  using (FAb; zeroᶠ; _+ᶠ_; negᶠ; neg-add)
open import Sovereign.Problem.Hodge.FreeAbBoundary
  using (C₀; C₁; ∂₁)

--------------------------------------------------------------------------------
-- §1. AC 机件（PropEq ⊕ 重排）
--------------------------------------------------------------------------------

ac3 : ∀ a b c → (a ⊕ b) ⊕ c ≡ (a ⊕ c) ⊕ b
ac3 a b c = trans (⊕-assoc a b c)
                  (trans (cong (a ⊕_) (⊕-comm b c)) (sym (⊕-assoc a c b)))

ac4 : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
ac4 a b c d =
  trans (⊕-assoc a b (c ⊕ d))
  (trans (cong (a ⊕_) h)
  (trans (sym (⊕-assoc a (b ⊕ d) c))
  (ac3 a (b ⊕ d) c)))
  where
    h : b ⊕ (c ⊕ d) ≡ (b ⊕ d) ⊕ c
    h = trans (⊕-comm b (c ⊕ d))
        (trans (⊕-assoc c d b)
        (trans (cong (c ⊕_) (⊕-comm d b)) (⊕-comm c (b ⊕ d))))

--------------------------------------------------------------------------------
-- §2. FAb 群律（逐点形态）
--------------------------------------------------------------------------------

neg-flip-r : ∀ a → a ⊕ negate a ≡ T₀
neg-flip-r T₀ = refl
neg-flip-r T₁ = refl
neg-flip-r T₂ = refl

+ᶠ-negᶠ-r : ∀ {n} (x : FAb n) (i : Fin n) → (x +ᶠ negᶠ x) i ≡ T₀
+ᶠ-negᶠ-r x i = neg-flip-r (x i)

neg-flip : ∀ a → negate a ⊕ a ≡ T₀
neg-flip T₀ = refl
neg-flip T₁ = refl
neg-flip T₂ = refl

+ᶠ-negᶠ-l : ∀ {n} (x : FAb n) (i : Fin n) → (negᶠ x +ᶠ x) i ≡ T₀
+ᶠ-negᶠ-l x i = neg-flip (x i)

neg-distrib : ∀ a b → negate (a ⊕ b) ≡ negate a ⊕ negate b
neg-distrib T₀ T₀ = refl
neg-distrib T₀ T₁ = refl
neg-distrib T₀ T₂ = refl
neg-distrib T₁ T₀ = refl
neg-distrib T₁ T₁ = refl
neg-distrib T₁ T₂ = refl
neg-distrib T₂ T₀ = refl
neg-distrib T₂ T₁ = refl
neg-distrib T₂ T₂ = refl

negᶠ-hom : ∀ {n} (x y : FAb n) (i : Fin n) →
           negᶠ (x +ᶠ y) i ≡ (negᶠ x +ᶠ negᶠ y) i
negᶠ-hom x y i = neg-distrib (x i) (y i)

--------------------------------------------------------------------------------
-- §3. 右分配（local——Trit 只有 distribˡ；经 comm ×2 + distribˡ 导出）
--------------------------------------------------------------------------------

distribʳ : ∀ a b → (a ⊕ b) ⊗ T₂ ≡ (a ⊗ T₂) ⊕ (b ⊗ T₂)
distribʳ a b =
  trans (⊗-comm (a ⊕ b) T₂)
        (trans (⊗-distribˡ-⊕ T₂ a b)
               (cong₂ _⊕_ (⊗-comm T₂ a) (⊗-comm T₂ b)))

--------------------------------------------------------------------------------
-- §4. ∂₁ 线性三条（K₃ 字面量表逐点）
--------------------------------------------------------------------------------

∂₁-add : ∀ (x y : FAb 3) (i : Fin 3) →
         ∂₁ (λ j → x j ⊕ y j) i ≡ (∂₁ x i) ⊕ (∂₁ y i)
∂₁-add x y fzero =
  trans (cong (λ u → u ⊕ (x₂ ⊕ y₂)) (distribʳ x₀ y₀))
        (ac4 (x₀ ⊗ T₂) (y₀ ⊗ T₂) x₂ y₂)
  where
    x₀ = x fzero; y₀ = y fzero
    x₂ = x (fsuc (fsuc fzero)); y₂ = y (fsuc (fsuc fzero))
∂₁-add x y (fsuc fzero) =
  trans (cong (λ u → (x₀ ⊕ y₀) ⊕ u) (distribʳ x₁ y₁))
        (ac4 x₀ y₀ (x₁ ⊗ T₂) (y₁ ⊗ T₂))
  where
    x₀ = x fzero; y₀ = y fzero
    x₁ = x (fsuc fzero); y₁ = y (fsuc fzero)
∂₁-add x y (fsuc (fsuc fzero)) =
  trans (cong (λ u → (x₁ ⊕ y₁) ⊕ u) (distribʳ x₂ y₂))
        (ac4 x₁ y₁ (x₂ ⊗ T₂) (y₂ ⊗ T₂))
  where
    x₁ = x (fsuc fzero); y₁ = y (fsuc fzero)
    x₂ = x (fsuc (fsuc fzero)); y₂ = y (fsuc (fsuc fzero))

--------------------------------------------------------------------------------
-- §5. ∂₁-neg 与 ∂₁-zero
--------------------------------------------------------------------------------

-- 辅助（3-case：negate/⊗ 表字面算术，全 refl）
neg⊗ : ∀ a → (negate a) ⊗ T₂ ≡ a
neg⊗ T₀ = refl
neg⊗ T₁ = refl
neg⊗ T₂ = refl

neg-otimes : ∀ a → negate (a ⊗ T₂) ≡ a
neg-otimes T₀ = refl
neg-otimes T₁ = refl
neg-otimes T₂ = refl

∂₁-neg : ∀ (x : FAb 3) (i : Fin 3) →
         ∂₁ (negᶠ x) i ≡ negate (∂₁ x i)
∂₁-neg x fzero =
  trans (cong (_⊕ (negate x₂)) (neg⊗ x₀))
        (sym (trans (neg-distrib (x₀ ⊗ T₂) x₂)
                    (cong (_⊕ (negate x₂)) (neg-otimes x₀))))
  where
    x₀ = x fzero; x₂ = x (fsuc (fsuc fzero))
∂₁-neg x (fsuc fzero) =
  trans (cong (negate x₀ ⊕_) (neg⊗ x₁))
        (sym (trans (neg-distrib x₀ (x₁ ⊗ T₂))
                    (cong (negate x₀ ⊕_) (neg-otimes x₁))))
  where
    x₀ = x fzero; x₁ = x (fsuc fzero)
∂₁-neg x (fsuc (fsuc fzero)) =
  trans (cong (negate x₁ ⊕_) (neg⊗ x₂))
        (sym (trans (neg-distrib x₁ (x₂ ⊗ T₂))
                    (cong (negate x₁ ⊕_) (neg-otimes x₂))))
  where
    x₁ = x (fsuc fzero); x₂ = x (fsuc (fsuc fzero))

zeroᶠ₃ : FAb 3
zeroᶠ₃ = λ _ → T₀

∂₁-zero : ∀ (i : Fin 3) → ∂₁ zeroᶠ₃ i ≡ T₀
∂₁-zero fzero = refl
∂₁-zero (fsuc fzero) = refl
∂₁-zero (fsuc (fsuc fzero)) = refl
