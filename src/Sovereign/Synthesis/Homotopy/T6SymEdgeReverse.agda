{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6SymEdgeReverse
--
-- **⑤ 的实例化**：`T6CayleySym` 的边是对称的 ⇒ `sym-edge` 可**构造**（不再是假设）
--
-- ## 为什么这是免费的
--
-- `T6SymEdge x y` 的两个构造子：
-- ```
--   inj₁ (j , p)   p : y ≡ updAt j x                    （+e_j）
--   inj₂ (j , p)   p : y ≡ updAt j (updAt j x)          （−e_j = 2 步）
-- ```
-- 两个方向**互逆**，而 `updAt` **三步归零**（`updAt-cubed`，特征 3）：
--
-- | 从 | 到 | 用 |
-- |---|---|---|
-- | `inj₁ (j , p)`（`+e_j`）| `inj₂ (j , _)`（`−e_j`）| `updAt j (updAt j (updAt j x)) ≡ x` |
-- | `inj₂ (j , p)`（`−e_j`）| `inj₁ (j , _)`（`+e_j`）| 同上 |
--
-- ⇒ 两个方向都用**同一条** `updAt-cubed` ✓ —— 特征 3 结构第 **五** 次直接送定理。
--
-- ## 收益
--
-- `AStepStdReverse.rev-cancel` 需要 `sym-edge` 作为假设；
-- 本模块给出它在 `T6CayleySym` 上的**实例** ⇒ `rev-cancel` 在该图上**无条件**可用 ✓
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyVec.updAt-cubed` 与 `T6CayleySym.T6SymEdge`（不重写）

module Sovereign.Synthesis.Homotopy.T6SymEdgeReverse where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec; updAt; updAt-cubed)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6CayleySym; T6SymEdge)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; nil; _++w_)
open import Sovereign.Synthesis.Homotopy.AStepStd using (AHomotopyStd)
open import Sovereign.Synthesis.Homotopy.AStepStdReverse using (rev-cancel)
open import Sovereign.Synthesis.Homotopy.AStepStdGroup using (rev)

--------------------------------------------------------------------------------
-- §1. ★★★ 边对称：`+e_j` 与 `−e_j` 互逆（靠 `updAt-cubed`）
--------------------------------------------------------------------------------

sym-edge-T6 : ∀ {n : ℕ} {x y : T6Vec n} → T6SymEdge x y → T6SymEdge y x
-- `+e_j`：`y ≡ updAt j x` ⇒ 反向是 `−e_j`：需要 `x ≡ updAt j (updAt j y)`
sym-edge-T6 (inj₁ (j , p)) =
  inj₂ (j , sym (trans (cong (updAt j) (cong (updAt j) p)) (updAt-cubed j _)))
-- `−e_j`：`y ≡ updAt j (updAt j x)` ⇒ 反向是 `+e_j`：需要 `x ≡ updAt j y`
sym-edge-T6 (inj₂ (j , p)) =
  inj₁ (j , sym (trans (cong (updAt j) p) (updAt-cubed j _)))

--------------------------------------------------------------------------------
-- §2. ★★★ 特化：`rev-cancel` 在 `T6CayleySym` 上**无条件**可用
--------------------------------------------------------------------------------

rev-cancel-T6 : ∀ {n : ℕ} {u v : T6Vec n} (p : Walk (T6CayleySym n) u v)
              → AHomotopyStd (T6CayleySym n) (p ++w rev sym-edge-T6 p) (nil u)
rev-cancel-T6 = rev-cancel sym-edge-T6
