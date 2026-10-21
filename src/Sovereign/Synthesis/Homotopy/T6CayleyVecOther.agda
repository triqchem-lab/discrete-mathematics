{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyVecOther
--
-- **`updAt` 不动别的坐标**（`T6CayleyCodeWalk` §7 与 `T6CayleyComm` §3 点名的「⑤ 不同坐标独立」）
--
-- ## 为什么需要
--
-- `π₁ᵈ(T6Cayley n) ≅ (C₃)ⁿ` 的「逐坐标计数」路线要求：沿坐标 `j` 走一步
-- **只改第 `j` 个坐标**。此前库里只有 `updAt-comm`（两个 `updAt` 可交换），
-- 但**没有**「`lookup i (updAt j v) ≡ lookup i v`（当 `i ≢ j`）」这一条。
--
-- ## 证法
--
-- 直接对 `Fin` 构造子分情况（`updAt` 的定义就是按 `Fin` 递归的）：
--   · `zero` vs `zero` ⇒ 与 `i ≢ j` 矛盾
--   · `zero` vs `suc`  ⇒ 两边都得 `a` ⇒ `refl`
--   · `suc`  vs `zero` ⇒ 两边都得 `lookup v i'` ⇒ `refl`
--   · `suc`  vs `suc`  ⇒ 归纳假设
--
-- ## 核心原则
--   · 0 postulate / 0 hole；复用 `updAt`（不重写）

module Sovereign.Synthesis.Homotopy.T6CayleyVecOther where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; _∷_; lookup)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

open import Sovereign.Synthesis.Homotopy.T6CayleyGraph using (succF3)
open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec; updAt; updAt-cubed; updAt-differs; succF3≢id)

--------------------------------------------------------------------------------
-- ★ `updAt j` 不改坐标 `i`（当 `i ≢ j`）
--------------------------------------------------------------------------------

updAt-other : ∀ {n : ℕ} (i j : Fin n) (v : T6Vec n)
            → ¬ (i ≡ j) → lookup (updAt j v) i ≡ lookup v i
updAt-other Fin.zero    Fin.zero    (a ∷ v) i≢j = ⊥-elim (i≢j refl)
updAt-other Fin.zero    (Fin.suc j) (a ∷ v) _   = refl
updAt-other (Fin.suc i) Fin.zero    (a ∷ v) _   = refl
updAt-other (Fin.suc i) (Fin.suc j) (a ∷ v) i≢j =
  updAt-other i j v (λ i≡j → i≢j (cong Fin.suc i≡j))
--------------------------------------------------------------------------------
-- §2. ★ 同一坐标的两个方向不同（`Nodup (neighbours x)` 的前置 ①）
--
-- 邻居表把 `updAt j x` 与 `updAt j (updAt j x)` 都收进去 ⇒ 若两者相等，表就有重复。
-- 本引理排除了这种情形（一行：由 `updAt-cubed` 把假设推成「`x` 等于 `updAt j x`」）。
--------------------------------------------------------------------------------

updAt-neq-two : ∀ {n : ℕ} (j : Fin n) (x : T6Vec n)
              → updAt j x ≢ updAt j (updAt j x)
updAt-neq-two j x h = updAt-differs j (updAt j x) (sym h)
--------------------------------------------------------------------------------
-- §3. ★ 不同坐标的两个方向不同（`Nodup (neighbours x)` 的前置 ②）
--
-- 思路：在坐标 `j` 上看。
--   · `lookup (updAt j x) j = succF3 (lookup x j)`（本模块 `lookup-updAt-same`）
--   · `lookup (updAt k x) j = lookup x j`        （§1 的 `updAt-other`，用 `j ≢ k`）
-- 若两者相等，就得到 `succF3 a ≡ a`，与已有的 `succF3≢id` 矛盾。
--------------------------------------------------------------------------------

lookup-updAt-same : ∀ {n : ℕ} (j : Fin n) (x : T6Vec n)
                  → lookup (updAt j x) j ≡ succF3 (lookup x j)
lookup-updAt-same Fin.zero    (a ∷ v) = refl
lookup-updAt-same (Fin.suc j) (a ∷ v) = lookup-updAt-same j v

updAt-neq-other : ∀ {n : ℕ} (j k : Fin n) (x : T6Vec n)
                → j ≢ k → updAt j x ≢ updAt k x
updAt-neq-other j k x j≢k h =
  succF3≢id (lookup x j)
    (trans (sym (lookup-updAt-same j x))
           (trans (cong (λ v → lookup v j) h)
                  (updAt-other j k x j≢k)))
--------------------------------------------------------------------------------
-- §4. ★ `updAt j x` 与「`k` 处加两步」不同（当 `j ≢ k`）
--
-- 仍在坐标 `j` 上看：左边是 `succF3 (lookup x j)`，右边（经两次 `updAt-other`）
-- 是 `lookup x j` ⇒ 与 `succF3≢id` 矛盾。
-- （这条是邻居表 `Nodup` 的跨项前置；与 §2/§3 合起来覆盖三类相邻对。）
--------------------------------------------------------------------------------

updAt-neq-other2 : ∀ {n : ℕ} (j k : Fin n) (x : T6Vec n)
                 → j ≢ k → updAt j x ≢ updAt k (updAt k x)
updAt-neq-other2 j k x j≢k h =
  succF3≢id (lookup x j)
    (trans (sym (lookup-updAt-same j x))
           (trans (cong (λ v → lookup v j) h)
                  (trans (updAt-other j k (updAt k x) j≢k)
                         (updAt-other j k x j≢k))))
--------------------------------------------------------------------------------
-- §5. ★ 对称变体：`updAt j (updAt j x)` 与 `updAt k x` 不同（`j ≢ k`）
--
-- 邻居表里「同一坐标的两个方向」与「其他坐标的一个方向」也会相邻 ⇒ 组装 `Unique`
-- 时需要的不是 §4 那条，而是它的**对称版**（错位一步）。
-- 坐标 `j` 上看：左边是 `succF3 (succF3 a)`，右边是 `a`。
--------------------------------------------------------------------------------

succF3≢id2 : (a : Fin 3) → succF3 (succF3 a) ≢ a
succF3≢id2 Fin.zero                     ()
succF3≢id2 (Fin.suc Fin.zero)           ()
succF3≢id2 (Fin.suc (Fin.suc Fin.zero)) ()

lookup-updAt-same2 : ∀ {n : ℕ} (j : Fin n) (x : T6Vec n)
                   → lookup (updAt j (updAt j x)) j ≡ succF3 (succF3 (lookup x j))
lookup-updAt-same2 j x =
  trans (lookup-updAt-same j (updAt j x)) (cong succF3 (lookup-updAt-same j x))

updAt-neq-other2' : ∀ {n : ℕ} (j k : Fin n) (x : T6Vec n)
                  → j ≢ k → updAt j (updAt j x) ≢ updAt k x
updAt-neq-other2' j k x j≢k h =
  succF3≢id2 (lookup x j)
    (trans (sym (lookup-updAt-same2 j x))
           (trans (cong (λ v → lookup v j) h)
                  (updAt-other j k x j≢k)))

