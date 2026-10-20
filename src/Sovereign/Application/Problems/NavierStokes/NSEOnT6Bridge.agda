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

open import Sovereign.Base.Trit using (Trit; _⊕_; negate) renaming (T₀ to Trit₀)
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

--------------------------------------------------------------------------------
-- §4. 双层差分与全算子对应
--------------------------------------------------------------------------------

-- 两层 `diffAt` 的对应：先逐层搬，再用 `shift-correspond'` 对齐**第一臂**
-- （第二臂两边完全相同 ⇒ 直接 `refl`）
diffAt2-correspond' : ∀ (i : Axis6) (f : ScalarField) (v : Torus 6) →
  diffAt i (diffAt i (λ w → f (vecToTuple w))) v ≡ diffF6 i (diffF6 i f) (vecToTuple v)
diffAt2-correspond' i f v =
  trans (cong₂ _⊕_
          (diffAt-correspond' i f (LN.shiftAt i v))
          (cong negate (diffAt-correspond' i f v)))
        (cong₂ _⊕_
          (cong (diffF6 i f) (shift-correspond' i v))
          refl)

-- ★ 全算子对应：`lapN {6}` 与 `laplacian6` 在桥下一致
--   （`sum6 a b c d e f = a ⊕ (b ⊕ (c ⊕ (d ⊕ (e ⊕ (f ⊕ T₀)))))` 与 `sumFin {6}` 同形状 ✓）
lapN-correspond : ∀ (f : ScalarField) (x : Torus6) →
  lapN {6} (λ v → f (vecToTuple v)) (tupleToVec x) ≡ laplacian6 f x
lapN-correspond f x =
  cong6-Trit-local
    (diffAt2-correspond' fzero f (tupleToVec x))
    (diffAt2-correspond' (fsuc fzero) f (tupleToVec x))
    (diffAt2-correspond' (fsuc (fsuc fzero)) f (tupleToVec x))
    (diffAt2-correspond' (fsuc (fsuc (fsuc fzero))) f (tupleToVec x))
    (diffAt2-correspond' (fsuc (fsuc (fsuc (fsuc fzero)))) f (tupleToVec x))
    (diffAt2-correspond' (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) f (tupleToVec x))
  where
    -- 六元同余（`sumFin {6}` 与 `sum6` 同形状，故直接 `cong₆`）
    cong6-Trit-local : ∀ {a b c d e f a' b' c' d' e' f' : Trit} →
      a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f ≡ f' →
      a ⊕ (b ⊕ (c ⊕ (d ⊕ (e ⊕ (f ⊕ Trit₀)))))
        ≡ a' ⊕ (b' ⊕ (c' ⊕ (d' ⊕ (e' ⊕ (f' ⊕ Trit₀)))))
    cong6-Trit-local refl refl refl refl refl refl = refl
