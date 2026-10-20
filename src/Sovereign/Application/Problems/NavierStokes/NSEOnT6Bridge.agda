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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; _⊕_; negate)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN as LN
  using (Torus; diffAt; lapN)
open import Sovereign.Application.Problems.NavierStokes.NSEOnT6SixAxis as NS
  using (Torus6; Axis6; ScalarField; diffF6; laplacian6)

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

--------------------------------------------------------------------------------
-- §3. 算子对应（T-E 后半）
--
-- 关键事实（先查过 ✓）：`sum6 a b c d e f = a ⊕ (b ⊕ (c ⊕ (d ⊕ (e ⊕ (f ⊕ T₀)))))`
--   与 `sumFin {6}` 的括号形状**完全相同** ⇒ 只需逐轴搬运 `diffAt` ✓
--------------------------------------------------------------------------------

-- 任意 `Vec 6` 版本的移位对应（`v` 必然是六元 ⇒ 可直接 pattern）
shift-correspond' : ∀ (i : Axis6) (v : Torus 6) →
  vecToTuple (LN.shiftAt i v) ≡ NS.shiftAt6 i (vecToTuple v)
shift-correspond' fzero (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) =
  cong (λ z → z , b , c , d , e , f) (sym (shift3-agree a))
shift-correspond' (fsuc fzero) (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) =
  cong (λ z → a , z , c , d , e , f) (sym (shift3-agree b))
shift-correspond' (fsuc (fsuc fzero)) (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) =
  cong (λ z → a , b , z , d , e , f) (sym (shift3-agree c))
shift-correspond' (fsuc (fsuc (fsuc fzero))) (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) =
  cong (λ z → a , b , c , z , e , f) (sym (shift3-agree d))
shift-correspond' (fsuc (fsuc (fsuc (fsuc fzero)))) (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) =
  cong (λ z → a , b , c , d , z , f) (sym (shift3-agree e))
shift-correspond' (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) =
  cong (λ z → a , b , c , d , e , z) (sym (shift3-agree f))

-- 任意 `v` 的单轴差分对应
diffAt-correspond' : ∀ (i : Axis6) (f : ScalarField) (v : Torus 6) →
  diffAt i (λ w → f (vecToTuple w)) v ≡ diffF6 i f (vecToTuple v)
diffAt-correspond' i f v =
  cong₂ _⊕_
    (cong f (shift-correspond' i v))
    refl

-- 两层 `diffAt` 的对应（消元的二阶差分类比）

-- ⛔ **待补（止损记录，第 4 次失败，2026-10-20）**：T-E 算子层
--
--   ① `diffAt2-correspond' : diffAt i (diffAt i (λ w → f (vecToTuple w))) v ≡ diffF6 i (diffF6 i f) (vecToTuple v)`
--   ② `lapN-correspond : lapN {6} (λ v → f (vecToTuple v)) (tupleToVec x) ≡ laplacian6 f x`
--
--   **已证可用件** ✓：`shift-correspond'`（任意 `v`，6 情形）、`diffAt-correspond'`（单层）
--
--   **卡点** ✗：`diffAt2-correspond'` 的右端需要把
--   `diffF6 i f (vecToTuple (LN.shiftAt i v))` 对齐成 `diffF6 i f (NS.shiftAt6 i (vecToTuple v))`，
--   这一步要靠 `cong (diffF6 i f) (shift-correspond' i v)`，但 `cong₂ _⊕_` 的两臂**形状不同步** ✗
--   （一臂已对齐、另一臂未对齐）⇒ 需要先把两臂**分别**对齐再拼，或改用 `subst`。
--
--   **下一轮正解**（不再盲试 ✗）：
--   先 `proof_goals action:"infer"` 打印 `diffAt2-correspond'` 的目标类型，
--   看清 `cong₂` 两臂的**具体形状差**，再决定是先 `cong` 对齐还是先 `trans` 分解。
--
--   注：`lapN-correspond` 依赖 ①，故一并待补。
