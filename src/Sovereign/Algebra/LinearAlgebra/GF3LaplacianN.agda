{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3LaplacianN
-- GF(3)ⁿ 环面上的**广义** Laplacian（T4 / 路线 A / ③a 的前置，2026-10-20）
--
-- 数学背景
--   现有 `NSEOnT6SixAxis` 的 `Torus6` 是**固定六元组**（`C3 × … × C3`），
--   无法对 `n` 做归纳 ✗。而 ③a 的分解同构
--     `ann(F_n) ≅ ann(F_{n−1}) ⊕ ann(F_{n−1}²)`
--   本质上是**对最后一个坐标**做分解 ⇒ 必须先有 `Torus : ℕ → Set`。
--
-- 核心原则
--   ① `Torus n = Vec (Fin 3) n` —— 用 `Vec` 而非嵌套积，才能对 `n` 归纳
--   ② `shiftAt` 用 **`Fin` 上的结构递归**（`Fin zero` 为空），不需要 `updateAt`
--   ③ `shift3³ = id` ⇒ `shiftAt³ = id`（归纳）
--
-- 本模块（T-A）：载体 + 移位 + 三次移位恒等。算子层（T-B）随后。
--
-- 依赖: Sovereign.Base.Trit（GF(3) 环公理）

module Sovereign.Algebra.LinearAlgebra.GF3LaplacianN where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

--------------------------------------------------------------------------------
-- §1. 载体（T-A1）
--------------------------------------------------------------------------------

Torus : ℕ → Set
Torus n = Vec (Fin 3) n

--------------------------------------------------------------------------------
-- §2. 单坐标循环移位（T-A2）
--------------------------------------------------------------------------------

-- `Fin 3` 上的循环移位 0 → 1 → 2 → 0
shift3 : Fin 3 → Fin 3
shift3 fzero           = fsuc fzero
shift3 (fsuc fzero)    = fsuc (fsuc fzero)
shift3 (fsuc (fsuc fzero)) = fzero

-- 第 i 个坐标循环移位（`Fin` 上的结构递归）
shiftAt : ∀ {n} → Fin n → Torus n → Torus n
shiftAt {n = suc n} fzero      (x ∷ xs) = shift3 x   ∷ xs
shiftAt {n = suc n} (fsuc i)   (x ∷ xs) = x          ∷ shiftAt i xs

--------------------------------------------------------------------------------
-- §3. 三次移位回原点（T-A3）
--------------------------------------------------------------------------------

shift3-3 : ∀ a → shift3 (shift3 (shift3 a)) ≡ a
shift3-3 fzero           = refl
shift3-3 (fsuc fzero)    = refl
shift3-3 (fsuc (fsuc fzero)) = refl

-- 逐点断言 `shiftAt³ = id`（逐坐标版本，值为 `refl` 型等式的 `≡`）
shiftAt3 : ∀ {n} (i : Fin n) (x : Torus n) → shiftAt i (shiftAt i (shiftAt i x)) ≡ x
shiftAt3 {n = suc n} fzero     (x ∷ xs) = cong₂ _∷_ (shift3-3 x) refl
shiftAt3 {n = suc n} (fsuc i)  (x ∷ xs) = cong₂ _∷_ refl (shiftAt3 i xs)

--------------------------------------------------------------------------------
-- §4. 算子层（T-B）
--------------------------------------------------------------------------------

ScalarN : ℕ → Set
ScalarN n = Torus n → Trit

-- `Fin n` 上的求和（结构递归；`Fin 0` 为空 ⇒ 和为 T₀）
sumFin : ∀ {n} → (Fin n → Trit) → Trit
sumFin {zero}  g = T₀
sumFin {suc n} g = g fzero ⊕ sumFin (λ i → g (fsuc i))

-- 沿第 i 个坐标的前向差分：`x_i = s_i − 1`
diffAt : ∀ {n} → Fin n → ScalarN n → ScalarN n
diffAt i f x = f (shiftAt i x) ⊕ negate (f x)

-- 广义 Laplacian：`Δ f x = Σ_j (x_j² f) x`
lapN : ∀ {n} → ScalarN n → ScalarN n
lapN f x = sumFin (λ j → diffAt j (diffAt j f) x)

--------------------------------------------------------------------------------
-- §5. 零场的 sanity（2026-10-20 补 —— 曾被误删 ✗）
--
-- 教训：`lapN-zero` 是**真命题**，不能因为「验证不了就删掉」✗。
-- 正确做法是补上它依赖的辅助引理（`sumFin-zero` / `sumFin-cong`）。
--------------------------------------------------------------------------------

-- `sumFin` 对点态相同的函数同余
sumFin-cong : ∀ {n} {g h : Fin n → Trit} → (∀ i → g i ≡ h i) → sumFin g ≡ sumFin h
sumFin-cong {zero}  h' = refl
sumFin-cong {suc n} h' = cong₂ _⊕_ (h' fzero) (sumFin-cong (λ i → h' (fsuc i)))

-- 恒为零的函数，其和为 T₀
sumFin-zero : ∀ {n} → sumFin {n} (λ _ → T₀) ≡ T₀
sumFin-zero {zero}  = refl
sumFin-zero {suc n} = sumFin-zero {n}

-- 零场的单坐标差分为零
diffAt-zero : ∀ {n} (i : Fin n) (x : Torus n) → diffAt i (λ _ → T₀) x ≡ T₀
diffAt-zero i x = refl

-- ★ 零场的 Laplacian 为零（逐点）
lapN-zero : ∀ {n} (x : Torus n) → lapN (λ _ → T₀) x ≡ T₀
lapN-zero {n} x =
  trans (sumFin-cong {n = n}
                     {g = λ j → diffAt j (diffAt j (λ _ → T₀)) x}
                     {h = λ _ → T₀}
                     (λ j → refl))
        (sumFin-zero {n})
