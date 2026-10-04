{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.FreeAbImEquiv
-- 任务书第二层·2.5 泛型化（GAP-M7a-im-equiv）：Σ 商等价的 isEquivRel 完整链
--
-- 数学背景（标准同调商形态）：
--   Im∂₁ y := Σ C₁ (λ b → ∀ i → y i ≡ ∂₁ b i)
--   ~₁ x y  := Im∂₁ (λ i → x i ⊕ negate (y i))   —— 即 x - y ∈ im ∂₁
--
--   isEquivRel 三义务完全归约为 **im ∂₁ 是子群**：
--     refl  : x ⊕ negᶠ x ≡ 0ᶠ 逐点（neg-flip-r）∈ im（0 ∈ im 由 ∂₁-zero）
--     sym   : negᶠ 封闭（∂₁-neg + negate 自逆 + comm）
--     trans : 加法封闭（∂₁-add + y 项相消链）
--   而 im 子群性完全归约为 **∂₁ 线性三条**（GAP-M7a-fab-laws 已闭合）。
--
-- 复用：FreeAbGroupLaws（neg-flip-r/neg-flip/neg-distrib/∂₁-add/∂₁-neg）。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.FreeAbImEquiv where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; negate; ⊕-assoc; ⊕-comm; ⊕-identityˡ)
open import Sovereign.Problem.Hodge.FreeAbBoundary using (C₀; C₁; ∂₁)
open import Sovereign.Algebra.FreeAbGroupLaws
  using (neg-flip-r; neg-flip; neg-distrib; ∂₁-add; ∂₁-neg; ∂₁-zero)

--------------------------------------------------------------------------------
-- §1. im ∂₁ 谓词（Σ 形态）与零链
--------------------------------------------------------------------------------

Im∂₁ : C₀ → Set
Im∂₁ y = Σ C₁ (λ b → ∀ i → y i ≡ (∂₁ b) i)

zeroC₀ : C₀
zeroC₀ = λ _ → T₀

zeroC₁ : C₁
zeroC₁ = λ _ → T₀

-- 0 ∈ im（∂₁-zero 逐点）
zero-in-im : Im∂₁ zeroC₀
zero-in-im = zeroC₁ , λ i → sym (∂₁-zero i)

-- negate 自逆
neg-self : ∀ v → negate (negate v) ≡ v
neg-self T₀ = refl
neg-self T₁ = refl
neg-self T₂ = refl

--------------------------------------------------------------------------------
-- §2. 逐点相消链：(x⊕neg y)⊕(y⊕neg z) ≡ x⊕neg z
--   （neg y 与 y 经 neg-flip 相消；assoc/identity 归位）
--------------------------------------------------------------------------------

cancel-pointwise : ∀ xv yv zv →
                   (xv ⊕ negate yv) ⊕ (yv ⊕ negate zv) ≡ xv ⊕ negate zv
cancel-pointwise xv yv zv =
  trans (⊕-assoc xv (negate yv) (yv ⊕ negate zv))
        (trans (cong (xv ⊕_) h) refl)
  where
    h : (negate yv) ⊕ (yv ⊕ negate zv) ≡ negate zv
    h = trans (sym (⊕-assoc (negate yv) yv (negate zv)))
        (trans (cong (_⊕ negate zv) (neg-flip yv))
               (⊕-identityˡ (negate zv)))

--------------------------------------------------------------------------------
-- §3. ~₁ 商等价三义务
--------------------------------------------------------------------------------

~₁ : C₀ → C₀ → Set
~₁ x y = Im∂₁ (λ i → x i ⊕ negate (y i))

-- ① refl：x - x = 0 ∈ im（neg-flip-r 逐点）
~₁-refl : ∀ x → ~₁ x x
~₁-refl x = zeroC₁ , λ i → trans (neg-flip-r (x i)) (sym (∂₁-zero i))

-- ② sym：x - y ∈ im ⟹ y - x ∈ im
--    ∂₁(negᶠ b) = negᶠ(∂₁ b) = negᶠ(x - y) = y - x（neg-distrib + neg-self + comm）
~₁-sym : ∀ x y → ~₁ x y → ~₁ y x
~₁-sym x y (b , hb) = (λ j → negate (b j)) , h'
  where
    h' : ∀ i → y i ⊕ negate (x i) ≡ (∂₁ (λ j → negate (b j))) i
    h' i = sym (trans (∂₁-neg b i)
           (trans (cong negate (sym (hb i)))
           (trans (neg-distrib (x i) (negate (y i)))
           (trans (cong (negate (x i) ⊕_) (neg-self (y i)))
                  (⊕-comm (negate (x i)) (y i))))))

-- ③ trans：x - y ∈ im ∧ y - z ∈ im ⟹ x - z ∈ im
--    witness b₁ +ᶠ b₂；相消链 + ∂₁-add
~₁-trans : ∀ x y z → ~₁ x y → ~₁ y z → ~₁ x z
~₁-trans x y z (b₁ , hb₁) (b₂ , hb₂) =
  (λ j → b₁ j ⊕ b₂ j) , h'
  where
    h' : ∀ i → x i ⊕ negate (z i) ≡ (∂₁ (λ j → b₁ j ⊕ b₂ j)) i
    h' i = trans (sym (cancel-pointwise (x i) (y i) (z i)))
                 (trans (cong₂ _⊕_ (hb₁ i) (hb₂ i))
                        (sym (∂₁-add b₁ b₂ i)))
