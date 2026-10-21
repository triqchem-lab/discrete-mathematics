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
open import Relation.Nullary using (yes; no; ¬_)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (allFinD; ∈-allFinD)
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (DecEq-T6Vec; decAt; decAt2; findEdgeDec; scanDec; P1; P2; _∉_; ∉-cons)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6SymEdge)
open import Sovereign.Synthesis.Homotopy.T6AStepCode2 using (TSet; StepCode)
open import Sovereign.Synthesis.Homotopy.T6AStepMap using (StepVertex; StepSide; decStepSide)
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
-- ## 关于「忠实性」（原写「⬜ 仍未做」，现已**证伪**，不是「未做」）
--
-- 原计划：「码 → 步的**忠实性**（不同码 ⇒ 不同步）」—— 这是**假的** ✗。
-- `T6AStepFaithful` 证明：`srcCode`/`tgtCode` **都不用 `ADir`**
-- ⇒ `mkStep dslide …` 与 `mkStep dexpand …` 共享**同一对走**却是**不同码**
-- ⇒ 不存在 `walks ↦ code` 的单射。
-- ✅ 可证的形态（已证）：**`ADir` 不影响走**（`srcCode-dir-irrel` / `tgtCode-dir-irrel`）
--   ⇒ `ADir` 只决定 `AHomotopy` 层用哪个方向（`toAHomotopyDir` 按它分派）。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §4. ★★ `findEdgeDec` 的**可靠 + 完备**（`T6CayleyDec` §8 的 **`Dec` 版**边查找）
--
-- `Dec` 版的 `no` 分支携带「真的没有边」的证明（靠 §5 的穷尽性引理），
-- 于是它比 `Maybe` 版强：`yes` 时给出见证，且**说 `no` 时有底**。
-- 两条都用同一个 `with` 判定器技巧（各 4 行）。
--------------------------------------------------------------------------------

findEdgeDec-sound : ∀ {n : ℕ} (x y : T6Vec n) → TSet (findEdgeDec x y) → T6SymEdge x y
findEdgeDec-sound x y h with findEdgeDec x y
... | yes p = p
... | no  _ = ⊥-elim h

-- ★ 完备性（同一个 `with` 技巧）：`no q` 支的 `q` 就是否命题 ⇒ 作用于 `h`
findEdgeDec-complete : ∀ {n : ℕ} (x y : T6Vec n) → T6SymEdge x y → TSet (findEdgeDec x y)
findEdgeDec-complete x y h with findEdgeDec x y
... | yes p = p
... | no  q = ⊥-elim (q h)

--------------------------------------------------------------------------------
-- §6. ★★ `decStepSide` 的可靠 + 完备（本链上最后一个未验证的判定器）
--
-- `decStepSide u c` 就是 `DecEq-T6Vec (proj₁ (interpC u (srcCode c))) (proj₁ (interpC u (tgtCode c)))`，
-- 而 `StepSide u c` 正是那两个投影相等 ⇒ 可靠性直接调 `DecEq-T6Vec-sound`；
-- 完备性用同一套 `with` 判定器写法（`no ¬p` 支的 `¬p` 就是否证）。
--------------------------------------------------------------------------------

decStepSide-sound : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n)
                  → TSet (decStepSide u c) → StepSide u c
decStepSide-sound u c = DecEq-T6Vec-sound _ _

decStepSide-complete : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n)
                     → StepSide u c → TSet (decStepSide u c)
decStepSide-complete u c h with decStepSide u c
... | yes p  = p
... | no  ¬p = ⊥-elim (¬p h)
