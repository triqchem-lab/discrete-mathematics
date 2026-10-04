{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.FreeAbImSubsetPlane
-- 任务书第二层·2.5 推进：im ∂₁ ⊆ 增广零平面（∑(∂₁x) ≡ 0）
--
-- 数学背景：K₃ 链群（FreeAb 载体）上，任意边链的边界在三个顶点上的
--   系数之和恒为零——im ∂₁ ⊆ { (a,b,c) : a+b+c ≡ 0 }（增广零平面）。
--   这是 H₀ = GF(3)³/im ∂₁ ≅ GF(3)（连通性）的两半之一。
--
-- 枚举口径：27 = 3³ case，恰在「≤27 case 允许枚举」阈值内。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.FreeAbImSubsetPlane where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.FreeAb using (FAb)
open import Sovereign.Problem.Hodge.FreeAbBoundary using (∂₁; C₁)

-- 三系数辅助边链
w₃ : Trit → Trit → Trit → C₁
w₃ a b c fzero                = a
w₃ a b c (fsuc fzero)         = b
w₃ a b c (fsuc (fsuc fzero)) = c

-- 三顶点系数和
sum₃ : Trit → Trit → Trit → Trit
sum₃ a b c =
  ((∂₁ (w₃ a b c)) fzero ⊕ (∂₁ (w₃ a b c)) (fsuc fzero)) ⊕
  (∂₁ (w₃ a b c)) (fsuc (fsuc fzero))

-- 增广零平面谓词（逐分量版）
InPlane₃ : Trit → Trit → Trit → Set
InPlane₃ a b c = sum₃ a b c ≡ T₀

-- 主定理：im ∂₁ ⊆ 增广零平面（27 case 枚举）
im-subset-plane₃ : ∀ (a b c : Trit) → InPlane₃ a b c
im-subset-plane₃ T₀ T₀ T₀ = refl
im-subset-plane₃ T₀ T₀ T₁ = refl
im-subset-plane₃ T₀ T₀ T₂ = refl
im-subset-plane₃ T₀ T₁ T₀ = refl
im-subset-plane₃ T₀ T₁ T₁ = refl
im-subset-plane₃ T₀ T₁ T₂ = refl
im-subset-plane₃ T₀ T₂ T₀ = refl
im-subset-plane₃ T₀ T₂ T₁ = refl
im-subset-plane₃ T₀ T₂ T₂ = refl
im-subset-plane₃ T₁ T₀ T₀ = refl
im-subset-plane₃ T₁ T₀ T₁ = refl
im-subset-plane₃ T₁ T₀ T₂ = refl
im-subset-plane₃ T₁ T₁ T₀ = refl
im-subset-plane₃ T₁ T₁ T₁ = refl
im-subset-plane₃ T₁ T₁ T₂ = refl
im-subset-plane₃ T₁ T₂ T₀ = refl
im-subset-plane₃ T₁ T₂ T₁ = refl
im-subset-plane₃ T₁ T₂ T₂ = refl
im-subset-plane₃ T₂ T₀ T₀ = refl
im-subset-plane₃ T₂ T₀ T₁ = refl
im-subset-plane₃ T₂ T₀ T₂ = refl
im-subset-plane₃ T₂ T₁ T₀ = refl
im-subset-plane₃ T₂ T₁ T₁ = refl
im-subset-plane₃ T₂ T₁ T₂ = refl
im-subset-plane₃ T₂ T₂ T₀ = refl
im-subset-plane₃ T₂ T₂ T₁ = refl
im-subset-plane₃ T₂ T₂ T₂ = refl

-- 包装：任意边链 x 的边界和为零（x 分解为其三系数）
im-subset-plane : ∀ (x : C₁) → InPlane₃ (x fzero) (x (fsuc fzero)) (x (fsuc (fsuc fzero)))
im-subset-plane x = im-subset-plane₃ (x fzero) (x (fsuc fzero)) (x (fsuc (fsuc fzero)))
