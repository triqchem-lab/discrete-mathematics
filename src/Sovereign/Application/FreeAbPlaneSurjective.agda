{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.FreeAbPlaneSurjective
-- 任务书第二层·2.5 推进：增广零平面的满性（平面 ⊆ im ∂₁——反向包含）
--
-- 数学背景：FreeAbImSubsetPlane 闭合了 im ∂₁ ⊆ 平面（正向）；本模块闭合
--   反向——**平面内任意 (a,b,c) 都有边链原像**，见证 x = (2a, c, 0)：
--     ∂₁ x v₀ = 2·(2a) + 0 = a（双倍还原 L1）
--     ∂₁ x v₁ = 2a + 2c = 2(a+c) ≡ 2·(2b) = b（L2 分配 + L3 前提转换 + L1）
--     ∂₁ x v₂ = c + 2·0 = c（refl）
--   与正向合成：im ∂₁ = 增广零平面（恰 2 维）——H₀ ≅ GF(3) 实例收官。
--
-- 三算术引理：
--   L1 双倍还原：(a⊗T₂)⊗T₂ ≡ a（3 refl；GF(3)：×4 ≡ ×1）
--   L2 ⊗T₂ 分配：(a⊕c)⊗T₂ ≡ (a⊗T₂)⊕(c⊗T₂)（复用 ⊗-distribˡ-⊕ + ⊗-comm）
--   L3 前提转换：(a⊕b)⊕c ≡ T₀ → (a⊕c) ≡ b⊗T₂（27 case 枚举：9 支成立 refl
--     + 18 支前提为构造子冲突假等式 λ ()——单层安全）
--
-- 复用：FreeAbBoundary（∂₁/C₁/w₃ 风格）、FreeAb、Base/Trit 全律。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.FreeAbPlaneSurjective where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂)
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_;
         ⊕-identityʳ; ⊗-comm; ⊗-distribˡ-⊕)
open import Sovereign.Algebra.FreeAb using (FAb)
open import Sovereign.Problem.Hodge.FreeAbBoundary using (∂₁; C₁)

--------------------------------------------------------------------------------
-- §1. 三算术引理
--------------------------------------------------------------------------------

-- L1 双倍还原：×4 ≡ ×1（GF(3)）
double-double : ∀ (a : Trit) → (a ⊗ T₂) ⊗ T₂ ≡ a
double-double T₀ = refl
double-double T₁ = refl
double-double T₂ = refl

-- L2 ⊗T₂ 分配（distribˡ + ⊗-comm）
mul2-distrib : ∀ (a c : Trit) → (a ⊕ c) ⊗ T₂ ≡ (a ⊗ T₂) ⊕ (c ⊗ T₂)
mul2-distrib a c =
  trans (⊗-comm (a ⊕ c) T₂)
  (trans (⊗-distribˡ-⊕ T₂ a c) (cong₂ _⊕_ (⊗-comm T₂ a) (⊗-comm T₂ c)))

-- L3 前提转换：(a⊕b)⊕c ≡ T₀ → a⊕c ≡ b⊗T₂（27 case 枚举）
premise-convert : ∀ (a b c : Trit) → (a ⊕ b) ⊕ c ≡ T₀ → (a ⊕ c) ≡ b ⊗ T₂
premise-convert T₀ T₀ T₀ h = refl
premise-convert T₀ T₀ T₁ ()
premise-convert T₀ T₀ T₂ ()
premise-convert T₀ T₁ T₀ ()
premise-convert T₀ T₁ T₁ ()
premise-convert T₀ T₁ T₂ h = refl
premise-convert T₀ T₂ T₀ ()
premise-convert T₀ T₂ T₁ h = refl
premise-convert T₀ T₂ T₂ ()
premise-convert T₁ T₀ T₀ ()
premise-convert T₁ T₀ T₁ ()
premise-convert T₁ T₀ T₂ h = refl
premise-convert T₁ T₁ T₀ ()
premise-convert T₁ T₁ T₁ h = refl
premise-convert T₁ T₁ T₂ ()
premise-convert T₁ T₂ T₀ h = refl
premise-convert T₁ T₂ T₁ ()
premise-convert T₁ T₂ T₂ ()
premise-convert T₂ T₀ T₀ ()
premise-convert T₂ T₀ T₁ h = refl
premise-convert T₂ T₀ T₂ ()
premise-convert T₂ T₁ T₀ h = refl
premise-convert T₂ T₁ T₁ ()
premise-convert T₂ T₁ T₂ ()
premise-convert T₂ T₂ T₀ ()
premise-convert T₂ T₂ T₁ ()
premise-convert T₂ T₂ T₂ h = refl

--------------------------------------------------------------------------------
-- §2. 预像见证与三面验证
--------------------------------------------------------------------------------

-- 预像：x = (2a, c, 0)
witness : ∀ (a b c : Trit) → C₁
witness a b c fzero                = a ⊗ T₂
witness a b c (fsuc fzero)         = c
witness a b c (fsuc (fsuc fzero)) = T₀

-- v₀ 分量：2·(2a) + 0 ≡ a
surj-v0 : ∀ (a b c : Trit) → (∂₁ (witness a b c)) fzero ≡ a
surj-v0 a b c = trans (cong₂ _⊕_ (double-double a) refl) (⊕-identityʳ a)

-- v₁ 分量：2a + 2c ≡ b（经 L2 + L3 + L1 链）
surj-v1 : ∀ (a b c : Trit) → (a ⊕ b) ⊕ c ≡ T₀ →
          (∂₁ (witness a b c)) (fsuc fzero) ≡ b
surj-v1 a b c h =
  trans (sym (mul2-distrib a c))
  (trans (cong (_⊗ T₂) (premise-convert a b c h)) (double-double b))

-- v₂ 分量：c + 2·0 ≡ c
surj-v2 : ∀ (a b c : Trit) → (∂₁ (witness a b c)) (fsuc (fsuc fzero)) ≡ c
surj-v2 a b c = ⊕-identityʳ c

--------------------------------------------------------------------------------
-- §3. 主定理：平面 ⊆ im ∂₁（反向包含；Σ-型原像见证）
--------------------------------------------------------------------------------

plane-surjective : ∀ (a b c : Trit) → (a ⊕ b) ⊕ c ≡ T₀ →
                   Σ C₁ (λ x →
                     ((∂₁ x) fzero ≡ a) ×
                     ((∂₁ x) (fsuc fzero) ≡ b) ×
                     ((∂₁ x) (fsuc (fsuc fzero)) ≡ c))
plane-surjective a b c h =
  witness a b c ,
  (surj-v0 a b c , (surj-v1 a b c h , surj-v2 a b c))
