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
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (DecEq-T6Vec; findEdgeDec)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6SymEdge)
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
-- §3. ★★ 完备性（相等 ⇒ 判定器说 yes）—— 与可靠性合起来，判定器「完全正确」
--------------------------------------------------------------------------------

-- 关键：`no q` 支给出的是 **`a ≢ b`**（否命题本身），可直接作用于 `eq`
-- ⇒ **不需要** stdlib 内部（`map′` / `×?`）的引理 ✓

DecEq-T6Vec-complete : ∀ {n : ℕ} (a b : T6Vec n)
                     → a ≡ b → TSet (DecEq-T6Vec a b)
DecEq-T6Vec-complete a b eq with DecEq-T6Vec a b
... | yes p = p
... | no  q = ⊥-elim (q eq)

decStepCode-complete : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n)
                     → StepVertex u c → TSet (decStepCode u c)
decStepCode-complete u c h with decStepCode u c
... | yes p = p
... | no  q = ⊥-elim (q h)

--------------------------------------------------------------------------------
-- §4. 小结
--
-- `DecEq-T6Vec` 与 `decStepCode` 现在 **可靠 + 完备**：
--   sound    : TSet d → 命题
--   complete : 命题 → TSet d
-- ⇒ 判定器不再是「未经校验的 oracle」，`toStepCode` 的前提**算得对**且**算得全**。
--
-- ## ⬜ 仍未做（如实标注）
-- · 「码 → 步的**忠实性**」（不同码 ⇒ 不同步）—— 需码层到步层的单射，尚属独立节点。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §4. ★★ `findEdgeDec` 的可靠性（`T6CayleyDec` §8 的 **`Dec` 版**边查找）
--
-- `Dec` 版的 `no` 分支携带「真的没有边」的证明（靠 §5 的穷尽性引理），
-- 于是它比 `Maybe` 版强：`yes` 时给出见证，且**说 `no` 时有底**。
-- 这里只补 `yes` 方向的可靠性（T-反射，一行）；`no` 方向已包含在 `findEdgeDec` 的构造里。
--------------------------------------------------------------------------------

findEdgeDec-sound : ∀ {n : ℕ} (x y : T6Vec n) → TSet (findEdgeDec x y) → T6SymEdge x y
findEdgeDec-sound x y h with findEdgeDec x y
... | yes p = p
... | no  _ = ⊥-elim h
