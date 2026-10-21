{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyNorm
--
-- **栈式单遍归约**：去掉 `fuel`，让归约成为**真正的函数**
--
-- ## 为什么要改
--
-- `T6CayleyCode.creduce` 带 `fuel` 参数，原因是普通结构递归在 `with` 内调用
-- 通不过终止检查（实测 `TerminationIssue`：`with` 抽象后原参数成 stuck 项）。
-- 带 `fuel` 的代价：它不是「`CWalk n` 的范式」，而是「`k` 步之内的范式」
-- ⇒ 任何关于它的定理都得多带一个参数。
--
-- **栈式（累加器）写法**消除这个代价：把已处理部分压在栈 `acc` 上。
-- 关键是**在 LHS 直接匹配 `acc`**（而不是 `with acc`）——
-- 这样 `with` 只抽象「决策」，不会抽象掉递归的候选参数 `xs` ✓
-- ⇒ **普通结构递归即可通过终止检查** ✓，不需要 `fuel`。
--
-- ```
--   cpassA acc       []         = reverse acc
--   cpassA []        (x ∷ xs)   = cpassA (x ∷ []) xs
--   cpassA (y ∷ acc') (x ∷ xs)  = 若 x 与 y 互逆 ⇒ cpassA acc' xs
--                                 否则           ⇒ cpassA (x ∷ y ∷ acc') xs
-- ```
-- 复杂度：每读一个元素最多一次比较（均摊）✓
--
-- ## ⚠ 本模块**只证**「这两个函数是什么」
--
-- 不证明它们是**范式**、也不证**范式唯一**（见 §3 的如实标注）。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyCode` 的 `CStep`/`CWalk`/`cstep-inv`/`DecEq-CStep`（不重写）

module Sovereign.Synthesis.Homotopy.T6CayleyNorm where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; reverse; [_])
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Synthesis.Homotopy.T6CayleyCode
  using (CStep; CWalk; cstep-inv; DecEq-CStep)

--------------------------------------------------------------------------------
-- §1. ★ 栈式单遍归约（**结构递归**，无 `fuel`）
--
-- 终止性：三个递归调用的第二参数分别是 `xs`（两次）与 `xs`，
-- 都是 `x ∷ xs` 的**结构子项** ⇒ 检查器只需看第二参数 ✓
--------------------------------------------------------------------------------

cpassA : ∀ {n : ℕ} (acc xs : CWalk n) → CWalk n
cpassA acc       []           = reverse acc
cpassA []        (x ∷ xs)     = cpassA (x ∷ []) xs
cpassA (y ∷ acc') (x ∷ xs) with DecEq-CStep x (cstep-inv y)
... | yes _ = cpassA acc' xs
... | no  _ = cpassA (x ∷ y ∷ acc') xs

-- 归约：空栈启动
creduceA : ∀ {n : ℕ} (w : CWalk n) → CWalk n
creduceA = cpassA []

--------------------------------------------------------------------------------
-- §2. 两个定义性事实（`refl` 级，用来确认实现确实按预期展开）
--------------------------------------------------------------------------------

creduceA-nil : ∀ {n : ℕ} → creduceA {n} [] ≡ []
creduceA-nil = refl

creduceA-single : ∀ {n : ℕ} (x : CStep n) → creduceA [ x ] ≡ [ x ]
creduceA-single x = refl

--------------------------------------------------------------------------------
-- §3. ⚠ 本模块**不**声称的（如实标注；这些都不是「顺手就能做」）
--
-- ① **消去律**：`creduceA ((cstep-inv y) ∷ y ∷ xs) ≡ creduceA xs`
--    —— 需要 `DecEq-CStep s s ≡ yes refl`（判定器在自反处的行为），
--       而 `DecEq-CStep` 是经 `Fin._≟_` 定义的 ⇒ 需要 `Fin` 的对应引理。
--    **未证**。
-- ② **范式性**：`creduceA` 的输出不含相邻逆对。**未证**。
-- ③ **幂等 / 范式唯一**。**未证**。
-- ④ **语义正确**：`creduceA` 不改变 `foldT`（`T6CayleyCodeWalk`）的终点。**未证**。
--
-- ⇒ 本模块的成立事实只有：`cpassA`/`creduceA` **存在、终止、按上述模式展开**
--   （外加 §2 两条 `refl`）。**不**包含任何「它是范式」的断言。
--------------------------------------------------------------------------------
