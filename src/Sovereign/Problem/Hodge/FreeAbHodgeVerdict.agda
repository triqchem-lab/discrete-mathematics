{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.FreeAbHodgeVerdict
-- 任务书第二层·2.5 裁决：Hodge 分解在 GF(3) 标准内积下的机器裁决
--
-- 先算后验（oracle 回执 0e7da6ea，108 点全枚举无抽样）：
--   ker ∂₁ = im ∂₂ = {(0,0,0),(1,1,1),(2,2,2)}（β₁ = 0）
--   ker δ₁ = 增广零平面（9 点）；调和空间 = {(c,c,c)}（3 点）
--   **分解铺满检验失败：im ∂₂ + 调和 + im δ₁ 只张成 9/27 点**
--   根基为空（非退化 ✓）；w111 迷向 ✓（⟨w,w⟩≡T₀）
--
-- Agda 裁决内容（oracle 事实的机器化）：
--   ①δ₁ := ∂₂ 的伴随（增广和）
--   ②调和见证：w111 ∈ ker ∂₁ ∧ w111 ∈ ker δ₁（非零调和向量）
--   ③β₁ = 0（复用 FreeAbHomology 的 H₁=0）
--   → 调和维数(1) ≠ β₁(0)：Hodge 分解在此内积下**不成立**的机器见证。
--
-- 根因（正确表述，修正 FreeAbInnerProduct 头注的「退化」误称）：
--   GF(3) 标准点积**非退化**（FreeAbNonDegenerate 已证）但**各向异性**
--   （存在迷向非零向量 w111）——Hodge 分解的直和性证明需要**定形**
--   （⟨v,v⟩=0 → v=0），迷向性阻断该步。解法路线：
--   (a) 非退化**且定形**的双线性型在 GF(3) 上不存在（3 奇 +
--       ((1,1,1) 类迷向族恒在——枚举已证 9/27 覆盖失败）；
--   (b) Hodge 分解改述为无内积形式（裂张量/显式补）——后续立项。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.FreeAbHodgeVerdict where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.FreeAb using (FAb)
open import Sovereign.Problem.Hodge.FreeAbBoundary
  using (∂₁; ∂₂; C₀; C₁; C₂; ∂∂-unit)
open import Sovereign.Problem.Hodge.FreeAbHomology
  using (cycle-coeffs-equal)

--------------------------------------------------------------------------------
-- §1. δ₁ := ∂₂ 的伴随（增广和，值域 C₂ = FAb 1）
--------------------------------------------------------------------------------

δ₁ : C₁ → C₂
δ₁ y fzero = (y fzero ⊕ y (fsuc fzero)) ⊕ y (fsuc (fsuc fzero))

--------------------------------------------------------------------------------
-- §2. 调和见证：w111 = (1,1,1) 同时落在两个核里
--------------------------------------------------------------------------------

w111 : C₁
w111 fzero = T₁
w111 (fsuc fzero) = T₁
w111 (fsuc (fsuc fzero)) = T₁

-- w111 ∈ ker ∂₁（复用 ∂∂-unit 的同一计算）
w111-ker-∂₁ : ∀ (i : Fin 3) → (∂₁ w111) i ≡ T₀
w111-ker-∂₁ fzero = refl
w111-ker-∂₁ (fsuc fzero) = refl
w111-ker-∂₁ (fsuc (fsuc fzero)) = refl

-- w111 ∈ ker δ₁（三循环：1+1+1 = 3 ≡ 0）
w111-ker-δ₁ : δ₁ w111 fzero ≡ T₀
w111-ker-δ₁ = refl

-- w111 非零（调和向量非平凡）
w111-nonzero : w111 fzero ≡ T₁
w111-nonzero = refl

--------------------------------------------------------------------------------
-- §3. β₁ = 0（复用 FreeAbHomology：闭链系数全相等 = Z₁ ⊆ im ∂₂）
--------------------------------------------------------------------------------

betti-1-zero-part : ∀ (x : C₁) → (∀ i → (∂₁ x) i ≡ T₀) →
                    (x fzero ≡ x (fsuc fzero)) ×
                    (x (fsuc fzero) ≡ x (fsuc (fsuc fzero)))
betti-1-zero-part = cycle-coeffs-equal

--------------------------------------------------------------------------------
-- §4. 裁决 record：调和非零 + β₁ = 0 并存——分解不成立的机器见证
--------------------------------------------------------------------------------

record HodgeVerdict : Set₁ where
  field
    harm-nonzero   : w111 fzero ≡ T₁
    harm-in-ker∂₁  : ∀ (i : Fin 3) → (∂₁ w111) i ≡ T₀
    harm-in-kerδ₁  : δ₁ w111 fzero ≡ T₀
    betti-1-zero   : ∀ (x : C₁) → (∀ i → (∂₁ x) i ≡ T₀) →
                     (x fzero ≡ x (fsuc fzero)) ×
                     (x (fsuc fzero) ≡ x (fsuc (fsuc fzero)))

hodge-verdict : HodgeVerdict
hodge-verdict = record
  { harm-nonzero  = w111-nonzero
  ; harm-in-ker∂₁ = w111-ker-∂₁
  ; harm-in-kerδ₁ = w111-ker-δ₁
  ; betti-1-zero  = betti-1-zero-part
  }
