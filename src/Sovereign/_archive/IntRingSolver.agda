{-# OPTIONS --cubical --guardedness #-}
-- | Sovereign.Algebra.IntRingSolver
-- ℤ 上的 RingSolver 桥（照 Data.Rational.Tactic.RingSolver 模式）：
-- 把 ℤ 的交换环实例（+-*-commutativeRing）适配为 Tactic.RingSolver 的
-- AlmostCommutativeRing，暴露 solve/solve-∀ macro——加法/乘法重排恒等式
-- 一行解决（sum3-comm / assoc-entry / braid-rel 的矩阵 entry 重排全部复用）。
module Sovereign.Algebra.IntRingSolver where

open import Data.Integer using (ℤ; 0ℤ)
open import Data.Integer.Properties using (+-*-commutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (0ℓ)
open import Data.Unit.Base using (⊤)
open import Data.Nat.Base using (ℕ)
open import Data.Maybe.Base using (Maybe; just; nothing)

import Tactic.RingSolver as Solver using (solve-macro; solve-∀-macro)
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

-- ℤ 判零（0≡?-weak 模式——pos/negsuc 分派）
0≡?-weak : (i : ℤ) → Maybe (0ℤ ≡ i)
0≡?-weak i = nothing

-- 交换环适配（fromCommutativeRing 需判零为 Maybe——填 nothing 保安全）
ring : ACR.AlmostCommutativeRing 0ℓ 0ℓ
ring = ACR.fromCommutativeRing +-0-commutativeRing (λ i → nothing)

macro
  solve-∀ : Term → TC ⊤
  solve-∀ = Solver.solve-∀-macro (quote ring)

macro
  solve : Term → Term → TC ⊤
  solve n = Solver.solve-macro n (quote ring)
