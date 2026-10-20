{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.NavierStokes.NSEOnT6Bridge
-- `Torus6`（六元组）与 `Torus 6`（`Vec`）的一致性桥（T4 / T-E，2026-10-20）
--
-- 为什么需要
--   `NSEOnT6SixAxis` 用固定六元组 `Torus6 = C3 × … × C3`（无法对 n 归纳 ✗）；
--   `GF3LaplacianN` 用 `Torus n = Vec (Fin 3) n`（可归纳 ✓）。
--   两者描述的是**同一个 729 点空间**，本模块给出显式换算与往返恒等，
--   为「把 `lapN` 的结论搬回 `laplacian6`」铺路。
--
-- 本模块（T-E 前半）：点类型换算 + 往返恒等 + 移位对应。
--
-- 依赖: Sovereign.Application.Problems.NavierStokes.NSEOnT6SixAxis（Torus6）
--       Sovereign.Algebra.LinearAlgebra.GF3LaplacianN（Torus / shiftAt）

module Sovereign.Application.Problems.NavierStokes.NSEOnT6Bridge where

open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN as LN using (Torus)
open import Sovereign.Application.Problems.NavierStokes.NSEOnT6SixAxis as NS
  using (Torus6; Axis6)

--------------------------------------------------------------------------------
-- §1. 点类型换算
--------------------------------------------------------------------------------

tupleToVec : Torus6 → Torus 6
tupleToVec (a , b , c , d , e , f) =
  a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []

vecToTuple : Torus 6 → Torus6
vecToTuple (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) =
  a , b , c , d , e , f

-- 往返恒等（两侧都是 `refl`：结构完全相同）
vecToTuple-tupleToVec : ∀ x → vecToTuple (tupleToVec x) ≡ x
vecToTuple-tupleToVec _ = refl

tupleToVec-vecToTuple : ∀ v → tupleToVec (vecToTuple v) ≡ v
tupleToVec-vecToTuple (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) = refl

--------------------------------------------------------------------------------
-- §2. 移位对应（`Axis6 = Fin 6`，故轴编号就是 `Fin 6` 的编号）
--------------------------------------------------------------------------------

-- 两处 `shift3` 是**不同定义**（都是 3-循环，但 Agda 视为不同）⇒ 显式一致性引理
shift3-agree : ∀ a → NS.shift3 a ≡ LN.shift3 a
shift3-agree fzero               = refl
shift3-agree (fsuc fzero)        = refl
shift3-agree (fsuc (fsuc fzero)) = refl

-- 六轴移位与 `Vec` 移位一致（6 情形，靠 `shift3-agree`）
shift-correspond : ∀ (i : Axis6) (x : Torus6) →
  tupleToVec (NS.shiftAt6 i x) ≡ LN.shiftAt i (tupleToVec x)
shift-correspond fzero (a , b , c , d , e , f) =
  cong (λ z → z ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) (shift3-agree a)
shift-correspond (fsuc fzero) (a , b , c , d , e , f) =
  cong (λ z → a ∷ z ∷ c ∷ d ∷ e ∷ f ∷ []) (shift3-agree b)
shift-correspond (fsuc (fsuc fzero)) (a , b , c , d , e , f) =
  cong (λ z → a ∷ b ∷ z ∷ d ∷ e ∷ f ∷ []) (shift3-agree c)
shift-correspond (fsuc (fsuc (fsuc fzero))) (a , b , c , d , e , f) =
  cong (λ z → a ∷ b ∷ c ∷ z ∷ e ∷ f ∷ []) (shift3-agree d)
shift-correspond (fsuc (fsuc (fsuc (fsuc fzero)))) (a , b , c , d , e , f) =
  cong (λ z → a ∷ b ∷ c ∷ d ∷ z ∷ f ∷ []) (shift3-agree e)
shift-correspond (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (a , b , c , d , e , f) =
  cong (λ z → a ∷ b ∷ c ∷ d ∷ e ∷ z ∷ []) (shift3-agree f)
