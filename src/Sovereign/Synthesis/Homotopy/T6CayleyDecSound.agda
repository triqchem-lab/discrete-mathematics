{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyDecSound
--
-- **判定器的可靠性**：`DecEq-T6Vec` 与 `decStepCode` 说 `yes` 时命题**真的成立**
--
-- ## 为什么需要
--
-- `decStepCode`（`T6AStepCodeMap` §7c）直接返回 `DecEq-T6Vec a b`，
-- 于是「判定器说能走一步」⇒「侧条件 `StepVertex u c` 成立」这一步**从未被证过** ✗
-- —— 用它的 `yes` 等于用公理（与本会话对 `DecEq-StepCode` 补 `sound`/`complete` 同一动机）。
--
-- ## 证法（关键：`T`-反射 + `with` 直接分情形）
--
-- `DecEq-T6Vec` / `decStepCode` 都是**结构性**函数（前者 = stdlib `≡-dec (Fin._≟_)`），
-- ⇒ 对它们的**返回值**做 `with` 分情形即可：
-- ```
--   ... | yes p = p          -- TSet (yes p) 归约为命题本身，p 就是证据
--   ... | no  q = ⊥-elim h   -- TSet (no q) 归约为 ⊥
-- ```
-- ⇒ **不需要** UIP / funext / stdlib 内部引理 ✓
-- （这正是 `T6AStepCode2` 里 `DecEq-StepCode-sound` 用的同一手法。）
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6AStepCode2.T` 与 `T6AStepCodeMap.decStepCode`（不重写）

module Sovereign.Synthesis.Homotopy.T6CayleyDecSound where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (DecEq-T6Vec)
open import Sovereign.Synthesis.Homotopy.T6AStepCode2 using (TSet; StepCode)
open import Sovereign.Synthesis.Homotopy.T6AStepMap using (StepVertex)
open import Sovereign.Synthesis.Homotopy.T6AStepCodeMap using (decStepCode)
open import Relation.Binary.PropositionalEquality using (_≡_)

--------------------------------------------------------------------------------
-- §1. ★ `DecEq-T6Vec` 的可靠性
--------------------------------------------------------------------------------

DecEq-T6Vec-sound : ∀ {n : ℕ} (a b : T6Vec n)
                  → TSet (DecEq-T6Vec a b) → a ≡ b
DecEq-T6Vec-sound a b h with DecEq-T6Vec a b
... | yes p = p
... | no  q = ⊥-elim h

--------------------------------------------------------------------------------
-- §2. ★★ `decStepCode` 的可靠性 —— `toStepCode` 的前提「可以算」且「算得对」
--------------------------------------------------------------------------------

decStepCode-sound : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n)
                  → TSet (decStepCode u c) → StepVertex u c
decStepCode-sound u c h with decStepCode u c
... | yes p = p
... | no  q = ⊥-elim h

--------------------------------------------------------------------------------
-- §3. ⬜ 未做（如实标注）
--
-- · **完备性** `StepVertex u c → TSet (decStepCode u c)`：需要 `DecEq-T6Vec` 的
--   **完备性**（相等 ⇒ `yes`），而 `≡-dec (Fin._≟_)` 的完备性依赖 stdlib 内部
--   （`map′` / `×?`）的 `T`-引理 —— 比可靠性贵得多，本模块未做。
-- · 「码 → 步的**忠实性**」（不同码 ⇒ 不同步）仍未做。
--------------------------------------------------------------------------------
