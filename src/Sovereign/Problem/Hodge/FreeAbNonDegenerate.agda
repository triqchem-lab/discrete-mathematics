{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.FreeAbNonDegenerate
-- 任务书第二层·2.5 修正：GF(3) 标准点积非退化——上一节点「退化」结论
--   系概念混淆（迷向 ≠ 退化），本模块机器修正。
--
--   迷向：∃w≠0, ⟨w,w⟩≡T₀（FreeAbInnerProduct 的 witness 实际证明的是这个）
--   退化：∃w≠0, ∀y, ⟨w,y⟩≡T₀（根基非零）——二者不同！
--   GF(3)^3 标准点积非退化：⟨x,eᵢ⟩≡xᵢ（对偶基读出），故 ∀y⟨x,y⟩≡0 ⟹ x≡0ᶠ 逐点。
--
--   特征 3 ≠ 2 ⟹ 对称双线性型标准理论（含 Hodge 分解正交补论证）可用
--   ——Hodge 分解 roadmap 解阻塞（改回可推进）。
--
-- 塔的说明：本工作系数域 = GF(3)（任务书基座，未越塔）；GF(3) ⊂ GF(9)
--   塔在库内（Algebra/GF9），后续需 GF(9) 系数再上塔。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.FreeAbNonDegenerate where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂)
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; ⊕-identityˡ; ⊕-identityʳ)
open import Sovereign.Algebra.FreeAb using (FAb)
open import Sovereign.Problem.Hodge.FreeAbBoundary using (C₁)
open import Sovereign.Problem.Hodge.FreeAbInnerProduct using (inner; w111)

--------------------------------------------------------------------------------
-- §1. 单位向量（生成元对偶基）
--------------------------------------------------------------------------------

e₀ e₁ e₂ : C₁
e₀ fzero = T₁
e₀ _ = T₀
e₁ (fsuc fzero) = T₁
e₁ _ = T₀
e₂ (fsuc (fsuc fzero)) = T₁
e₂ _ = T₀

--------------------------------------------------------------------------------
-- §2. 算术小引理
--------------------------------------------------------------------------------

⊗T₁-id : ∀ (a : Trit) → a ⊗ T₁ ≡ a
⊗T₁-id T₀ = refl
⊗T₁-id T₁ = refl
⊗T₁-id T₂ = refl

⊗T₀-zero : ∀ (a : Trit) → a ⊗ T₀ ≡ T₀
⊗T₀-zero T₀ = refl
⊗T₀-zero T₁ = refl
⊗T₀-zero T₂ = refl

--------------------------------------------------------------------------------
-- §3. 求值引理：⟨x,eᵢ⟩ ≡ xᵢ（对偶基读出）
--------------------------------------------------------------------------------

inner-e₀ : ∀ (x : C₁) → inner x e₀ ≡ x fzero
inner-e₀ x =
  trans (cong (λ u → (u ⊕ (x (fsuc fzero) ⊗ T₀)) ⊕ (x (fsuc (fsuc fzero)) ⊗ T₀))
              (⊗T₁-id (x fzero)))
  (trans (cong (λ u → (x fzero ⊕ u) ⊕ (x (fsuc (fsuc fzero)) ⊗ T₀))
              (⊗T₀-zero (x (fsuc fzero))))
  (trans (cong (λ u → (x fzero ⊕ T₀) ⊕ u) (⊗T₀-zero (x (fsuc (fsuc fzero)))))
  (trans (cong (_⊕ T₀) (⊕-identityʳ (x fzero))) (⊕-identityʳ (x fzero)))))

inner-e₁ : ∀ (x : C₁) → inner x e₁ ≡ x (fsuc fzero)
inner-e₁ x =
  trans (cong (λ u → (u ⊕ (x (fsuc fzero) ⊗ T₁)) ⊕ (x (fsuc (fsuc fzero)) ⊗ T₀))
              (⊗T₀-zero (x fzero)))
  (trans (cong (λ u → (T₀ ⊕ u) ⊕ (x (fsuc (fsuc fzero)) ⊗ T₀))
              (⊗T₁-id (x (fsuc fzero))))
  (trans (cong (λ u → u ⊕ (x (fsuc (fsuc fzero)) ⊗ T₀))
              (⊕-identityˡ (x (fsuc fzero))))
  (trans (cong (λ u → x (fsuc fzero) ⊕ u) (⊗T₀-zero (x (fsuc (fsuc fzero)))))
         (⊕-identityʳ (x (fsuc fzero))))))

inner-e₂ : ∀ (x : C₁) → inner x e₂ ≡ x (fsuc (fsuc fzero))
inner-e₂ x =
  trans (cong (λ u → (u ⊕ (x (fsuc fzero) ⊗ T₀)) ⊕ (x (fsuc (fsuc fzero)) ⊗ T₁))
              (⊗T₀-zero (x fzero)))
  (trans (cong (λ u → (T₀ ⊕ u) ⊕ (x (fsuc (fsuc fzero)) ⊗ T₁))
              (⊗T₀-zero (x (fsuc fzero))))
  (trans (cong (λ u → T₀ ⊕ u) (⊗T₁-id (x (fsuc (fsuc fzero)))))
         (⊕-identityˡ (x (fsuc (fsuc fzero))))))

--------------------------------------------------------------------------------
-- §4. 非退化性：∀y⟨x,y⟩≡0 ⟹ 逐分量 xᵢ≡0（根基为零机器证明）
--------------------------------------------------------------------------------

non-degenerate-0 : ∀ (x : C₁) → (∀ (y : C₁) → inner x y ≡ T₀) → x fzero ≡ T₀
non-degenerate-0 x h = trans (sym (inner-e₀ x)) (h e₀)

non-degenerate-1 : ∀ (x : C₁) → (∀ (y : C₁) → inner x y ≡ T₀) →
                   x (fsuc fzero) ≡ T₀
non-degenerate-1 x h = trans (sym (inner-e₁ x)) (h e₁)

non-degenerate-2 : ∀ (x : C₁) → (∀ (y : C₁) → inner x y ≡ T₀) →
                   x (fsuc (fsuc fzero)) ≡ T₀
non-degenerate-2 x h = trans (sym (inner-e₂ x)) (h e₂)

non-degenerate : ∀ (x : C₁) → (∀ (y : C₁) → inner x y ≡ T₀) →
                 (x fzero ≡ T₀) × (x (fsuc fzero) ≡ T₀) ×
                 (x (fsuc (fsuc fzero)) ≡ T₀)
non-degenerate x h =
  non-degenerate-0 x h , (non-degenerate-1 x h , non-degenerate-2 x h)

--------------------------------------------------------------------------------
-- §5. 迷向 ≠ 退化：w111 迷向但不在根基（修正上一节点的概念混淆）
--------------------------------------------------------------------------------

w111-not-in-radical : ¬ (∀ (y : C₁) → inner w111 y ≡ T₀)
w111-not-in-radical h = w111-nonzero (non-degenerate-0 w111 h)
  where
    w111-nonzero : ¬ (w111 fzero ≡ T₀)
    w111-nonzero ()
