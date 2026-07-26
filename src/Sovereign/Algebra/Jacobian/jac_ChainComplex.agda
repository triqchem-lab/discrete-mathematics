{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Algebra.Jacobian.jac_ChainComplex where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record ChainComplex (len : ℕ) : Set where
  field
    dimC      : ℕ → ℕ
    rank∂     : ℕ → ℕ
    nullity∂  : ℕ → ℕ
    dimℋ      : ℕ → ℕ          -- 调和维数 (独立于 dimH)
    hodge-decomp : ∀ k → nullity∂ k ≡ rank∂ (suc k) + dimℋ k
      -- Hodge分解: ker(∂_k) = im(∂_{k+1}) ⊕ ℋ_k

dimH : ∀ {len} → ChainComplex len → ℕ → ℕ
dimH C k = nullity∂ k ∸ rank∂ (suc k) where open ChainComplex C

-- 定理: dimℋ = dimH (非定义相等)
-- 证明: (a+b)∸a = b, 令 a=rank_{k+1}, b=dimℋ_k
--   dimH = nullity ∸ rank_{k+1} = (rank_{k+1}+dimℋ) ∸ rank_{k+1} = dimℋ

-- 三角复形实例
dimC3 rank3 : ℕ → ℕ
dimC3 0 = 3; dimC3 1 = 3; dimC3 _ = 0
rank3 0 = 0; rank3 1 = 2; rank3 _ = 0
null3 : ℕ → ℕ; null3 k = dimC3 k ∸ rank3 k
dimℋ3 : ℕ → ℕ; dimℋ3 0 = 1; dimℋ3 1 = 1; dimℋ3 _ = 0
hodge3 : ∀ k → null3 k ≡ rank3 (suc k) + dimℋ3 k
hodge3 0 = refl; hodge3 1 = refl
hodge3 (suc (suc k)) = refl

tri : ChainComplex 2
tri = record { dimC = dimC3; rank∂ = rank3; nullity∂ = null3; dimℋ = dimℋ3; hodge-decomp = hodge3 }

tri-H0 : dimH tri 0 ≡ 1; tri-H0 = refl
tri-H1 : dimH tri 1 ≡ 1; tri-H1 = refl
