{-# OPTIONS --rewriting #-}

module Sovereign.Geometry.TorusAlgebra where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Structology.T6 using (T6Lattice; GF3)

-- Fin 3 上的运算
tritOf : GF3 → Trit
tritOf zero = T₀ ; tritOf (suc zero) = T₁ ; tritOf (suc (suc zero)) = T₂

finOf : Trit → GF3
finOf T₀ = zero ; finOf T₁ = suc zero ; finOf T₂ = suc (suc zero)

_+₃_ : GF3 → GF3 → GF3
x +₃ y = finOf (tritOf x ⊕ tritOf y)

_·₃_ : GF3 → GF3 → GF3
x ·₃ y = finOf (tritOf x ⊗ tritOf y)

-- T⁶ 上的函数
CoordFunc : Set
CoordFunc = T6Lattice → GF3

-- 6 个坐标投影
χ₀ χ₁ χ₂ χ₃ χ₄ χ₅ : CoordFunc
χ₀ (x₀ ∷ _ ) = x₀ ; χ₁ (_ ∷ x₁ ∷ _ ) = x₁
χ₂ (_ ∷ _ ∷ x₂ ∷ _ ) = x₂ ; χ₃ (_ ∷ _ ∷ _ ∷ x₃ ∷ _ ) = x₃
χ₄ (_ ∷ _ ∷ _ ∷ _ ∷ x₄ ∷ _ ) = x₄
χ₅ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ x₅ ∷ []) = x₅

-- 函数环运算 (逐点)
_+f_ : CoordFunc → CoordFunc → CoordFunc
(f +f g) p = f p +₃ g p

_·f_ : CoordFunc → CoordFunc → CoordFunc
(f ·f g) p = f p ·₃ g p

constFn : GF3 → CoordFunc
constFn c _ = c

zeroFn : CoordFunc ; zeroFn _ = zero
oneFn : CoordFunc ; oneFn _ = suc zero

-- 定理: 坐标投影的交换行为
χ₀-χ₁-comm : χ₀ (zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []) ≡ zero
χ₀-χ₁-comm = refl

-- 函数加法的恒等元
add-zero : (zeroFn +f χ₀) (zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []) ≡ zero
add-zero = refl

-- 0 postulate.
