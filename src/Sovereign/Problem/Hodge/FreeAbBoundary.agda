{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.FreeAbBoundary
-- 任务书第二层·2.1 收官 + 2.5 解阻塞：FreeAb 载体上的泛型边界算子与
--   ∂∘∂ ≡ 0 主定理（K₃ 填充三角实例）
--
-- 数学背景：单纯链群 C₂ --∂₂--> C₁ --∂₁--> C₀（系数 GF(3)），
--   载体用 FreeAb（FAb n = Fin n → Trit，见 Sovereign.Algebra.FreeAb）：
--     C₀ = FAb 3（3 顶点）、C₁ = FAb 3（3 边）、C₂ = FAb 1（1 面）
--
--   定向约定（循环边向）：e₀₁ = [v₀,v₁]、e₁₂ = [v₁,v₂]、e₂₀ = [v₂,v₀]
--     ∂₁ e₀₁ = v₁ ⊖ v₀ = 2v₀ + v₁（GF(3)：⊖ = +2）
--     ∂₁ e₁₂ = 2v₁ + v₂
--     ∂₁ e₂₀ = 2v₂ + v₀
--     ∂₂ t   = e₀₁ + e₁₂ + e₂₀（循环和——**GF(3) 特有**：1+1+1 = 3 ≡ 0，
--              这正是 EckmannNonSplitting 见证的特征 3 现象的另一面）
--
--   主定理：∂₁ ∘ ∂₂ ≡ 0（逐点）——符号消去的根基是 neg-add
--   （2a + a ≡ T₀，三循环）。
--
-- ⚠ 诚实边界：K₃ 实例（3-0-1 维）；全泛型 SimplicialComplex record +
--   面恒等式字段为路径 A roadmap。
--
-- 复用：FreeAb（载体与逐点代数）、Base/Trit（算术）、BoundaryGF3（语义锚——
--   本模块是同一 ∂∂=0 定理在 FreeAb 泛型载体上的重述）。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.FreeAbBoundary where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.FreeAb
  using (FAb; zeroᶠ; _+ᶠ_; neg-add)

--------------------------------------------------------------------------------
-- §1. 链群（FreeAb 实例化）
--------------------------------------------------------------------------------

C₀ C₁ C₂ : Set
C₀ = FAb 3   -- 顶点链
C₁ = FAb 3   -- 边链（循环定向 e₀₁/e₁₂/e₂₀）
C₂ = FAb 1   -- 面链（唯一 2-单形 t = [v₀,v₁,v₂]）

--------------------------------------------------------------------------------
-- §2. 边界算子
--
--   ∂₁ : C₁ → C₀（逐点三分支）
--   ∂₂ : C₂ → C₁（系数复制——循环定向下 ∂₂t = e₀₁+e₁₂+e₂₀）
--------------------------------------------------------------------------------

∂₁ : C₁ → C₀
∂₁ x fzero        = (x fzero ⊗ T₂) ⊕ x (fsuc (fsuc fzero))   -- 2e₀₁ + e₂₀ @ v₀
∂₁ x (fsuc fzero) = (x fzero) ⊕ (x (fsuc fzero) ⊗ T₂)        -- e₀₁ + 2e₁₂ @ v₁
∂₁ x (fsuc (fsuc fzero)) =
  (x (fsuc fzero)) ⊕ (x (fsuc (fsuc fzero)) ⊗ T₂)            -- e₁₂ + 2e₂₀ @ v₂

∂₂ : C₂ → C₁
∂₂ x fzero                = x fzero
∂₂ x (fsuc fzero)         = x fzero
∂₂ x (fsuc (fsuc fzero)) = x fzero

--------------------------------------------------------------------------------
-- §3. 主定理：∂₁ ∘ ∂₂ ≡ 0（逐点；3 顶点 × 3 系数 = 9 case，每支经 neg-add）
--------------------------------------------------------------------------------

∂∂-zero : ∀ (c : C₂) (i : Fin 3) → (∂₁ (∂₂ c)) i ≡ T₀
-- v₀：2(c₀) + c₀ ≡ 0
∂∂-zero c fzero = neg-add (c fzero)
-- v₁：c₀ + 2c₀ ≡ 0（⊕-comm 归入 neg-add）
∂∂-zero c (fsuc fzero) = sym-helper (c fzero)
  where
    sym-helper : ∀ (a : Trit) → a ⊕ (a ⊗ T₂) ≡ T₀
    sym-helper a = comm-helper a
      where
        comm-helper : ∀ (a : Trit) → a ⊕ (a ⊗ T₂) ≡ T₀
        comm-helper T₀ = refl
        comm-helper T₁ = refl
        comm-helper T₂ = refl
-- v₂：c₀ + 2c₀ ≡ 0（同上）
∂∂-zero c (fsuc (fsuc fzero)) = sym-helper2 (c fzero)
  where
    sym-helper2 : ∀ (a : Trit) → a ⊕ (a ⊗ T₂) ≡ T₀
    sym-helper2 a = comm-helper2 a
      where
        comm-helper2 : ∀ (a : Trit) → a ⊕ (a ⊗ T₂) ≡ T₀
        comm-helper2 T₀ = refl
        comm-helper2 T₁ = refl
        comm-helper2 T₂ = refl

--------------------------------------------------------------------------------
-- §4. 具体核对：生成元层面的 ∂ 表（refl 计算，衔接 BoundaryGF3 语义）
--------------------------------------------------------------------------------

-- ∂₂(单位面) = (1,1,1)——循环和系数
∂₂-unit : ∂₂ (λ _ → T₁) fzero ≡ T₁
∂₂-unit = refl

-- ∂₁(∂₂(单位面)) 在三顶点上全为 T₀
∂∂-unit-0 : (∂₁ (∂₂ (λ _ → T₁))) fzero ≡ T₀
∂∂-unit-0 = refl

∂∂-unit-1 : (∂₁ (∂₂ (λ _ → T₁))) (fsuc fzero) ≡ T₀
∂∂-unit-1 = refl

∂∂-unit-2 : (∂₁ (∂₂ (λ _ → T₁))) (fsuc (fsuc fzero)) ≡ T₀
∂∂-unit-2 = refl
