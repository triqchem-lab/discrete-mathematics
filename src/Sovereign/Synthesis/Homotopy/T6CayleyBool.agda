{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyBool
--
-- **`Bool` 决策器**：绕开「`Dec` 的见证需要无关性」这堵墙
--
-- ## 为什么要这套东西
--
-- 台账 `PN.B4.deceq-reflection-wall` 记了一个真障碍：
-- 要证 `DecEq-CStep x y ≡ yes p`（或 `≡ no ¬p`）需要
-- **`CStep` 的 UIP**（`yes` 侧）或 **funext**（`no` 侧）——本库纯 PropEq 下都没有。
--
-- **绕过路**：不用 `Dec`，改用 `Bool`，并把「可信」做成**定理**：
--
-- | 件 | 陈述 |
-- |---|---|
-- | `finEqB` | `toℕ i ≡ᵇ toℕ j` —— **在 `ℕ` 上**比较（不携带证明）|
-- | `finEqB-complete` | `i ≡ j → finEqB i j ≡ true` |
-- | `finEqB-sound` | `finEqB i j ≡ true → i ≡ j` |
-- | `cdEqB` | `CStep n → CStep n → Bool`（判定 `x ≡ cstep-inv y`，4 情形）|
-- | `cdEqB-complete` / `cdEqB-sound` | 两个方向 |
--
-- **关键**：`Bool` 的 `≡ true` 是**诚实的等式**（不携带证明）⇒
-- 关于它的推理不需要 UIP / funext ✓ —— 这正是本线第五次用「换到不带证明的载体」这一手法。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `Data.Nat.Properties` 的 `≡ᵇ⇒≡` / `≡⇒≡ᵇ` 与 `Data.Fin.Properties` 的 `toℕ-injective`

module Sovereign.Synthesis.Homotopy.T6CayleyBool where

open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero; suc)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Sovereign.Synthesis.Homotopy.T6CayleyCode
  using (CStep; cplus; cminus; cstep-inv)
open import Sovereign.Synthesis.Homotopy.T6CayleyNorm using (cfin)

--------------------------------------------------------------------------------
-- §1. ★ 在 ℕ 上比较 `Fin` 元素（不携带证明）
--------------------------------------------------------------------------------

finEqB : ∀ {n : ℕ} (i j : Fin n) → Bool
finEqB i j = Fin.toℕ i ≡ᵇ Fin.toℕ j

finEqB-complete : ∀ {n : ℕ} (i j : Fin n) → i ≡ j → T (finEqB i j)
finEqB-complete i .i refl = ≡⇒≡ᵇ (Fin.toℕ i) (Fin.toℕ i) refl

finEqB-sound : ∀ {n : ℕ} (i j : Fin n) → T (finEqB i j) → i ≡ j
finEqB-sound i j h = toℕ-injective (≡ᵇ⇒≡ (Fin.toℕ i) (Fin.toℕ j) h)

--------------------------------------------------------------------------------
-- §2. ★ 判定 `x ≡ cstep-inv y`（4 情形，无证明分量）
--
-- 注意 `cstep-inv (cplus k) = cminus k`（定义性）⇒ 同向的两个情形恒为 `false`。
--------------------------------------------------------------------------------

cdEqB : ∀ {n : ℕ} (x y : CStep n) → Bool
cdEqB (cplus j)  (cplus k)  = false
cdEqB (cplus j)  (cminus k) = finEqB j k
cdEqB (cminus j) (cplus k)  = finEqB j k
cdEqB (cminus j) (cminus k) = false

--------------------------------------------------------------------------------
-- §3. ★★ 两个方向（「可信」是**定理**，不是假设）
--------------------------------------------------------------------------------

cdEqB-complete : ∀ {n : ℕ} (x y : CStep n) → x ≡ cstep-inv y → T (cdEqB x y)
cdEqB-complete (cplus j)  (cplus k)  ()
cdEqB-complete (cplus j)  (cminus k) p = finEqB-complete j k (suc-inj p)
  where
    suc-inj : cplus j ≡ cplus k → j ≡ k
    suc-inj = cong cfin
cdEqB-complete (cminus j) (cplus k)  p = finEqB-complete j k (suc-inj p)
  where
    suc-inj : cminus j ≡ cminus k → j ≡ k
    suc-inj = cong cfin
cdEqB-complete (cminus j) (cminus k) ()

cdEqB-sound : ∀ {n : ℕ} (x y : CStep n) → T (cdEqB x y) → x ≡ cstep-inv y
cdEqB-sound (cplus j)  (cplus k)  h = ⊥-elim h
cdEqB-sound (cplus j)  (cminus k) h = cong cplus (finEqB-sound j k h)
cdEqB-sound (cminus j) (cplus k)  h = cong cminus (finEqB-sound j k h)
cdEqB-sound (cminus j) (cminus k) h = ⊥-elim h

--------------------------------------------------------------------------------
-- §4. ⬜ 下一步（判据明确）
--
-- ① `cpassB`（结构同 `cpassS`，`Dec` 换 `Bool`）；
-- ② 在 `cpassB` 上重证 ①（范式性）/ ③（语义正确）—— 形状相同；
-- ③ **②（幂等）** —— 现在 `≡ true` 是诚实等式，`with` 分支可自由推理。
--------------------------------------------------------------------------------
