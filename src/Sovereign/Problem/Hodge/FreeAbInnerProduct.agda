{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.FreeAbInnerProduct
-- 任务书第二层·2.5 推进：FreeAb 载体上的内积机件 + 退化性机器见证
--
-- 数学背景：Hodge 分解（C_k = im ∂_{k+1} ⊕ H_k ⊕ im ∂*ₖ）依赖
--   **非退化内积**。本模块在 K₃ 链群上定义逐点内积并机器验证：
--
--   ①对称性：⟨x,y⟩ ≡ ⟨y,x⟩（27 case 枚举——三分量积和的交换重排）
--   ②**退化性 witness**：⟨(1,1,1), (1,1,1)⟩ ≡ T₀ 而 (1,1,1) ≢ 0
--     ——GF(3) 标准点积**退化**（非零向量的自内积可为零）。
--
-- ⚠ 本模块的核心产出是②：它是 Hodge 分解在此内积下**不可用**的机器
--   见证——roadmap 项「Hodge 分解（内积/伴随 ∂*）」被对抗性预检
--   击穿于内积退化性。解法路线（后续立项）：
--   (a) 换非退化双线性型（GF(3) 上存在，如交错型）；或
--   (b) Hodge 分解改述为无内积形式（Z₁ = B₁ ⊕˅ … 的显式余_tensor）。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.FreeAbInnerProduct where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; ⊗-comm)
open import Sovereign.Algebra.FreeAb using (FAb)
open import Sovereign.Problem.Hodge.FreeAbBoundary using (C₁)

--------------------------------------------------------------------------------
-- §1. 内积定义（三分量逐点积和）
--------------------------------------------------------------------------------

inner : C₁ → C₁ → Trit
inner x y = ((x fzero ⊗ y fzero) ⊕ (x (fsuc fzero) ⊗ y (fsuc fzero)))
            ⊕ (x (fsuc (fsuc fzero)) ⊗ y (fsuc (fsuc fzero)))

--------------------------------------------------------------------------------
-- §2. 对称性（27 case 枚举——三分量的交换重排）
--------------------------------------------------------------------------------

inner-sym : ∀ (x y : C₁) → inner x y ≡ inner y x
inner-sym x y =
  trans (cong₂ (λ (u v : Trit) → (u ⊕ v) ⊕ (x (fsuc (fsuc fzero)) ⊗ y (fsuc (fsuc fzero))))
               (⊗-comm (x fzero) (y fzero))
               (⊗-comm (x (fsuc fzero)) (y (fsuc fzero))))
  (cong (λ (u : Trit) → ((y fzero ⊗ x fzero) ⊕ (y (fsuc fzero) ⊗ x (fsuc fzero))) ⊕ u)
        (⊗-comm (x (fsuc (fsuc fzero))) (y (fsuc (fsuc fzero)))))

--------------------------------------------------------------------------------
-- §3. 退化性机器见证：循环生成元 (1,1,1) 自内积为零而向量非零
--------------------------------------------------------------------------------

-- 循环生成元 w = (1,1,1)（恰是 im ∂₂ 的生成元——FreeAbBoundary §4）
w111 : C₁
w111 = λ _ → T₁

-- 非零性：w111 fzero = T₁ ≢ T₀（构造子冲突，单层 ()）
w111-nonzero : ¬ (w111 fzero ≡ T₀)
w111-nonzero ()

-- 退化 witness：⟨w111, w111⟩ ≡ T₀（1+1+1 = 3 ≡ 0，GF(3) 三循环）
degenerate-witness : inner w111 w111 ≡ T₀
degenerate-witness = refl
