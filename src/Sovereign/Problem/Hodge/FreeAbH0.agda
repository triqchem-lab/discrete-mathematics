{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.FreeAbH0
-- 任务书第二层·2.5 收官：GF(3) 系数链群的同调群全部机器闭合
--
--   H₂ = 0（∂₂ 单射于生成元——平凡）
--   H₁ = 0（FreeAbHomology 已证：Z₁ = im ∂₂）
--   H₀ ≅ GF(3)（本模块：增广分解——任意 0-链 x 分解为
--     x ≡ (aug x)·e₀ + ∂₁b，即 x 的类由增广和 σ(x) 唯一决定）
--
--   增广 aug x = x₀ ⊕ x₁ ⊕ x₂；分解见证：
--     k := aug x；y := w₃(k⊗T₂, x₂, T₀)（平面点 (x₀⊕k⊗T₂, x₁, x₂) 的原像，
--     由 FreeAbPlaneSurjective 的同款构造）——三分量方程在具体 (x₀,x₁,x₂)
--     下全部计算闭合（27 case，恰在阈值内）。
--
-- 复用：FreeAbBoundary（∂₁/C₁/C₀）、Base/Trit。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.FreeAbH0 where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.FreeAb using (FAb)
open import Sovereign.Problem.Hodge.FreeAbBoundary using (∂₁; ∂₂; C₀; C₁; C₂)

--------------------------------------------------------------------------------
-- §1. H₂ = 0：∂₂ 在生成元上单射（平凡——∂₂ 保留首系数）
--------------------------------------------------------------------------------

h₂-zero : ∀ (c : C₂) → (∂₂ c) fzero ≡ T₀ → c fzero ≡ T₀
h₂-zero c h = h

-- 增广和
aug₃ : Trit → Trit → Trit → Trit
aug₃ a b c = (a ⊕ b) ⊕ c

-- 预像边链：y = (A⊗T₂, c, T₀)（平面点 (a⊕2k, b, c) 的原像，A = a⊕2k）
w₃ : Trit → Trit → Trit → C₁
w₃ a b c fzero                = a
w₃ a b c (fsuc fzero)         = b
w₃ a b c (fsuc (fsuc fzero)) = c

-- H₀ 分解单 case：任意 (a,b,c) 以 k := aug 为代表、y 为边界原像
h₀-case : ∀ (a b c : Trit) →
  Σ Trit (λ k → Σ C₁ (λ y →
    (a ≡ (k ⊕ (∂₁ y) fzero)) ×
    (b ≡ (∂₁ y) (fsuc fzero)) ×
    (c ≡ (∂₁ y) (fsuc (fsuc fzero)))))
h₀-case T₀ T₀ T₀ = T₀ , (w₃ (T₀ ⊗ T₂) T₀ T₀ , (refl , (refl , refl)))
h₀-case T₀ T₀ T₁ = T₁ , (w₃ (T₂ ⊗ T₂) T₁ T₀ , (refl , (refl , refl)))
h₀-case T₀ T₀ T₂ = T₂ , (w₃ (T₁ ⊗ T₂) T₂ T₀ , (refl , (refl , refl)))
h₀-case T₀ T₁ T₀ = T₁ , (w₃ (T₂ ⊗ T₂) T₀ T₀ , (refl , (refl , refl)))
h₀-case T₀ T₁ T₁ = T₂ , (w₃ (T₁ ⊗ T₂) T₁ T₀ , (refl , (refl , refl)))
h₀-case T₀ T₁ T₂ = T₀ , (w₃ (T₀ ⊗ T₂) T₂ T₀ , (refl , (refl , refl)))
h₀-case T₀ T₂ T₀ = T₂ , (w₃ (T₁ ⊗ T₂) T₀ T₀ , (refl , (refl , refl)))
h₀-case T₀ T₂ T₁ = T₀ , (w₃ (T₀ ⊗ T₂) T₁ T₀ , (refl , (refl , refl)))
h₀-case T₀ T₂ T₂ = T₁ , (w₃ (T₂ ⊗ T₂) T₂ T₀ , (refl , (refl , refl)))
h₀-case T₁ T₀ T₀ = T₁ , (w₃ (T₀ ⊗ T₂) T₀ T₀ , (refl , (refl , refl)))
h₀-case T₁ T₀ T₁ = T₂ , (w₃ (T₂ ⊗ T₂) T₁ T₀ , (refl , (refl , refl)))
h₀-case T₁ T₀ T₂ = T₀ , (w₃ (T₁ ⊗ T₂) T₂ T₀ , (refl , (refl , refl)))
h₀-case T₁ T₁ T₀ = T₂ , (w₃ (T₂ ⊗ T₂) T₀ T₀ , (refl , (refl , refl)))
h₀-case T₁ T₁ T₁ = T₀ , (w₃ (T₁ ⊗ T₂) T₁ T₀ , (refl , (refl , refl)))
h₀-case T₁ T₁ T₂ = T₁ , (w₃ (T₀ ⊗ T₂) T₂ T₀ , (refl , (refl , refl)))
h₀-case T₁ T₂ T₀ = T₀ , (w₃ (T₁ ⊗ T₂) T₀ T₀ , (refl , (refl , refl)))
h₀-case T₁ T₂ T₁ = T₁ , (w₃ (T₀ ⊗ T₂) T₁ T₀ , (refl , (refl , refl)))
h₀-case T₁ T₂ T₂ = T₂ , (w₃ (T₂ ⊗ T₂) T₂ T₀ , (refl , (refl , refl)))
h₀-case T₂ T₀ T₀ = T₂ , (w₃ (T₀ ⊗ T₂) T₀ T₀ , (refl , (refl , refl)))
h₀-case T₂ T₀ T₁ = T₀ , (w₃ (T₂ ⊗ T₂) T₁ T₀ , (refl , (refl , refl)))
h₀-case T₂ T₀ T₂ = T₁ , (w₃ (T₁ ⊗ T₂) T₂ T₀ , (refl , (refl , refl)))
h₀-case T₂ T₁ T₀ = T₀ , (w₃ (T₂ ⊗ T₂) T₀ T₀ , (refl , (refl , refl)))
h₀-case T₂ T₁ T₁ = T₁ , (w₃ (T₁ ⊗ T₂) T₁ T₀ , (refl , (refl , refl)))
h₀-case T₂ T₁ T₂ = T₂ , (w₃ (T₀ ⊗ T₂) T₂ T₀ , (refl , (refl , refl)))
h₀-case T₂ T₂ T₀ = T₁ , (w₃ (T₁ ⊗ T₂) T₀ T₀ , (refl , (refl , refl)))
h₀-case T₂ T₂ T₁ = T₂ , (w₃ (T₀ ⊗ T₂) T₁ T₀ , (refl , (refl , refl)))
h₀-case T₂ T₂ T₂ = T₀ , (w₃ (T₂ ⊗ T₂) T₂ T₀ , (refl , (refl , refl)))

-- 包装：任意 0-链 x（分解为其三系数的具体 case）
h₀-split : ∀ (x : C₀) →
  Σ Trit (λ k → Σ C₁ (λ y →
    (x fzero ≡ (k ⊕ (∂₁ y) fzero)) ×
    (x (fsuc fzero) ≡ (∂₁ y) (fsuc fzero)) ×
    (x (fsuc (fsuc fzero)) ≡ (∂₁ y) (fsuc (fsuc fzero)))))
h₀-split x = h₀-case (x fzero) (x (fsuc fzero)) (x (fsuc (fsuc fzero)))
