{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.AStepStdOnCayley
--
-- **C3-a 的可行性检查**：`AStepStd` 在裁决指定的 Cayley 载体上**还剩几个生成元可用？**
--
-- ## 为什么必须先做这一检查
--
-- 人类裁决把 C3-a 定为「用 `AStepStd`（三角 + 方形 + 回溯）作等价关系，定义**新对象**
-- `π₁ᵈˢᵗᵈ`，验证是否 ≅ C₃」。但 `AStepStd` 的三个生成元**各自需要额外的边**：
--
-- | 生成元 | 需要的边 | `T6Cayley n` 有吗 |
-- |---|---|---|
-- | `tri-slide` | 有向三角形 `x→y→z` **且** 弦 `x→z` | ❌ 无（已证 `tfN`：该图无有向三角形）|
-- | `bt` | **回溯对** `e : x→y`、`f : y→x` | ❌ 无（本模块 `no-backtrack`）|
-- | `sq-slide4` | 4-循环 `x→y→z→w` **且** 弦 `x→w` | ⚠ 未定（§3 给出论证思路，但未形式化）|
--
-- 而裁决 2 步 1 把 Cayley 图定义为「**边 = 加生成元 `e_j`**」（只有 `+e_j`，**没有 `-e_j`**）。
-- ⇒ 前两个生成元在该载体上**根本不可用**。
--
-- ## 结论
--
-- **⇒ C3-a 若照裁决 2 步 1 的字面载体做，`π₁ᵈˢᵗᵈ(T¹)` 仍不会 ≅ C₃** ——
--   让 C₃ 塌缩所需的 `bt` 在该载体上不存在。
--   要真正得到 C₃，载体必须**对称化**（含 `±e_j`：`x ↦ x ± e_j` 都是边）。
--   这一点已入 `journal` 待裁决 —— **C3-a 需要人类指定生成元集（`+e_j` 还是 `±e_j`）**。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `T6CayleyTriangleFree` 的 `tfN` / `succF3≢id` / `succF3²≢id` /
--     `stepGen-yes` / `stepGen-no`（不重证）

module Sovereign.Synthesis.Homotopy.AStepStdOnCayley where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)

open import Sovereign.Synthesis.Homotopy.T6CayleyGraph using (T6Vert; succF3; stepGen; T6Cayley)
open import Sovereign.Synthesis.Homotopy.T6CayleyTriangleFree
  using (tfN; succF3²≢id; stepGen-yes; stepGen-no)
open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (succF3≢id)

--------------------------------------------------------------------------------
-- §1. 边的展开形式（复用 `T6Cayley` 的 `edge`）
--------------------------------------------------------------------------------

EdgeAt : ∀ {n : ℕ} → T6Vert n → T6Vert n → Set
EdgeAt {n} x y = Σ (Fin n) (λ j → y ≡ stepGen j x)

--------------------------------------------------------------------------------
-- §2. ★★ `bt` 不可用：没有回溯对
--
-- 若 `x →j y`（即 `y ≡ stepGen j x`）且 `y →k x`（即 `x ≡ stepGen k y`），
-- 则 `x ≡ stepGen k (stepGen j x)`。在坐标 `k`（或 `j`）上取矛盾：
--   · `k ≢ j`：`x k ≡ succF3 (x k)` ✗
--   · `k ≡ j`：`x j ≡ succF3 (succF3 (x j))` ✗
--------------------------------------------------------------------------------

no-backtrack : ∀ {n : ℕ} (x y : T6Vert n)
             → EdgeAt x y → EdgeAt y x → ⊥
no-backtrack x y (j , e1) (k , e2) with k Fin.≟ j

-- `k ≢ j`：取坐标 k
... | no ¬kj =
      succF3≢id (x k)
        (sym (trans (cong (λ f → f k) h)
              (trans (stepGen-yes k (stepGen j x) k refl)
                     (cong succF3 (stepGen-no j x k ¬kj)))))
  where
    h : x ≡ stepGen k (stepGen j x)
    h = trans e2 (cong (stepGen k) e1)

-- `k ≡ j`：取坐标 j（+2 对 +0）
... | yes kj =
      succF3²≢id (x j)
        (sym (trans (cong (λ f → f j) h)
              (trans (stepGen-yes k (stepGen j x) j (sym kj))
                     (cong succF3 (stepGen-yes j x j refl)))))
  where
    h : x ≡ stepGen k (stepGen j x)
    h = trans e2 (cong (stepGen k) e1)

--------------------------------------------------------------------------------
-- §3. `tri-slide` 不可用：无有向三角形（= `tfN` 的直译）
--
-- §4 的 `sq-slide4` **未定**：它需要「三步 `stepGen` 等于一步」。
-- 论证思路（未形式化）：把三个生成元索引按坐标计数，得每坐标的 `succF3` 幂次
-- ∈ {0,1,2,3}；一步只有 {0,1}。相等要求逐坐标幂次相同 ⇒ 总计数 3 = 1 ⇒
-- 必有坐标计数 3（幂 3 ≡ 0 vs 1 ⇒ `succF3 a ≡ a` ✗）或计数 2（幂 2 vs 1 ⇒
-- `succF3² a ≡ succF3 a` ✗）或两坐标各 1（另一坐标 1 vs 0 ⇒ `succF3 a ≡ a` ✗）
-- ⇒ 三种都不可能。形式化需引入「按坐标计数」，属独立任务。
--------------------------------------------------------------------------------

no-triangle : ∀ (n : ℕ) (x y z : T6Vert n)
            → EdgeAt x y → EdgeAt y z → EdgeAt x z → ⊥
no-triangle n x y z = tfN n {x} {y} {z}
