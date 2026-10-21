{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyIdem
--
-- **② 幂等**：`creduceB' w = reverse (creduceB w)` 是幂等的
--
-- ## 为什么是 `creduceB'` 而不是 `creduceB`
--
-- oracle 全枚举（回执 `0c189883`）已定：
--
-- | 函数 | 幂等？ |
-- |---|---|
-- | `creduceS`（= `creduceB`，栈序输出）| ❌ **假**（4056 反例，例 `ab → ba`）|
-- | `creduceA`（= `reverse ∘ creduceS` = `creduceB'`）| ✅ **真**（0 反例）|
--
-- ⇒ ② 的正确陈述是 **`creduceB'` 幂等**，等价于（`reverse` 单射）：
-- ```
--   creduceB (reverse (creduceB w)) ≡ creduceB w
-- ```
--
-- ## 证明路线
--
-- 核心是**「已归约的栈，反向处理回来还是它」**：
-- ```
--   cpassB-self : NoCancel v → cpassB [] (reverse v) ≡ v
-- ```
-- 因为把 `reverse v` 逐个压栈（若无消去）得到的是 `reverse (reverse v) = v` ✓
-- 而「无消去」由 `NoCancel v` 加 **相邻关系对称**（`adj-sym'`）给出 ✓
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyBool` 的 `cpassB`/`cdEqB-¬` 与 `T6CayleyNorm` 的 `NoCancel`/`adj-sym'`

module Sovereign.Synthesis.Homotopy.T6CayleyIdem where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; reverse; _++_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk; cstep-inv)
open import Sovereign.Synthesis.Homotopy.T6CayleyNorm
  using (NoCancel; nc-nil; nc-one; nc-two; adj-sym')
open import Sovereign.Synthesis.Homotopy.T6CayleyBool
  using (cpassB; creduceB; cdEqB; cdEqB-¬; cdEqB-sound)

--------------------------------------------------------------------------------
-- §2. ★★ 主引理：已归约的栈反向处理回来还是它
--
-- ⚠ 本条**未完成** —— 下面只给出已证部分的骨架；`TODO` 处是写不出来的地方。
--   保留在盘上（按纪律：WIP 原样保留 + journal 登记），不伪装成已证。
--------------------------------------------------------------------------------

-- 已证的小件：`NoCancel` 给出「栈顶两元素不互逆」的直接投影
NoCancel-head : ∀ {n : ℕ} (x y : CStep n) (xs : CWalk n)
              → NoCancel (x ∷ y ∷ xs) → ¬ (x ≡ cstep-inv y)
NoCancel-head x y xs (nc-two .x .y .xs ¬p _) = ¬p

-- 已证的小件：`NoCancel` 的尾部
NoCancel-tail₂ : ∀ {n : ℕ} (x y : CStep n) (xs : CWalk n)
               → NoCancel (x ∷ y ∷ xs) → NoCancel (y ∷ xs)
NoCancel-tail₂ x y xs (nc-two .x .y .xs _ t) = t

--------------------------------------------------------------------------------
-- §3. ⬜ 未完成（**如实保留**，不伪装）
--
-- 待证：
--   `cpassB-self : ∀ v → NoCancel v → cpassB [] (reverse v) ≡ v`
--   `creduceB'-idem : ∀ w → reverse (creduceB (reverse (creduceB w))) ≡ reverse (creduceB w)`
--
-- 已定位的难点：对 `v` 归纳时，`reverse (x ∷ xs) = reverse xs ++ [x]`
-- 把「最后一个元素」推到**末尾**，而 `cpassB` 是**从头部**递归的
-- ⇒ 归纳假设作用在 `reverse xs` 上，而 `x` 却出现在**最后**
-- ⇒ 需要一条「把元素追加到已处理部分」的辅助递归（而不是 `cpassB` 的头部递归）。
--------------------------------------------------------------------------------
