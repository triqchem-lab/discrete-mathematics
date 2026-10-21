{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.UniversalAlgebra.PresentationTheorems
--
-- **`Presentation` 的普遍定理**（不依赖 DC 的特殊结构）。
--
-- ## 定位：普遍约束 vs DC 巧合（2026-10-21 人类澄清）
--
-- `Presentation` 是**通用模板**，字段必须是**所有**满足八要素的结构都成立的约束。
-- 因此：
--
--   · **`g ≠ unit`** —— ✅ **普遍成立**：只依赖 `zeroʳ` + `clock-min`
--     + `1 < phase-order` + `phase-order ∣ clock`，**与 DC 无关** ✓
--   · **G3 单边 / N8 / N3b** —— ❌ **不是普遍约束** ✗：
--     当前 record 没有任何字段连接 `phase` 与 `step` ✗
--     ⇒ 它们是**额外公理**（写进模板 = 过拟合 DC ✗）
--     ⇒ 应作为 `dc-presentation` 的**额外定理** ✓
--     （若将来把「分量直积」写进模板，它们才成为定理 —— 见 §2 的条件性说明）
--
-- ## 核心原则
--   · 定理以**假设**形式给出（不修改模板 ✗）
--   · 证明只用 `zeroʳ` + 假设 ⇒ **零 postulate** ✓
--   · 不引入 DC 的特定结构（`Trit`/`AlphaPower` 不出现）✓

module Sovereign.Algebra.UniversalAlgebra.PresentationTheorems where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Nat.Divisibility using (_∣_; ∣⇒≤)
open import Data.Nat.Properties using (<⇒≤; ≤-trans; <⇒≱; ≤-refl)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (NonZero; ≢-nonZero)

-- `m < n ⇒ NonZero n`
<⇒NonZero : ∀ {m n} → m < n → NonZero n
<⇒NonZero {m} {zero}  ()
<⇒NonZero {m} {suc n} _ = ≢-nonZero (λ ())
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open import Sovereign.Algebra.UniversalAlgebra.Presentation using (Presentation; iterate)

--------------------------------------------------------------------------------
-- §1. ★★ 普遍定理：`g ≠ unit`
--------------------------------------------------------------------------------

-- 周期的定义（`clock-cycle` 的假设形态）
Period : ∀ {A : Set} → (A → A) → ℕ → Set
Period {A} f k = ∀ (x : A) → iterate f k x ≡ x

-- ★★★ **普遍定理**：`g ≢ unit`
--
-- 假设（都是八要素的普遍约束）：
--   ① `1 < phase-order`         —— 相位非平凡
--   ② `clock-min`               —— `clock` 整除任何周期
--   ③ `phase-order ∣ clock`     —— 相位阶整除时钟
--
-- 证明：若 `g = unit`，则 `step y g = y`（`zeroʳ`）⇒ `1` 是周期
--       ⇒ `clock ∣ 1` ⇒ `clock ≤ 1` ✗
--       但 ①③ ⇒ `1 < phase-order ≤ clock` ⇒ `clock ≥ 2` ✗ 矛盾
--
-- ⚠ 本定理**不涉及 DC 的任何特殊结构** ✓ —— 对任意 `Presentation A` 成立 ✓
g-ne-unit : ∀ {A : Set} (P : Presentation A)
  (0<clk : 0 < Presentation.clock P)
  (1<po : 1 < Presentation.phase-order P)
  (clock-min : ∀ k → Period (λ y → Presentation.step P y (Presentation.g P)) k
                     → Presentation.clock P ∣ k)
  (po∣clk : Presentation.phase-order P ∣ Presentation.clock P)
  → Presentation.g P ≢ Presentation.unit P
g-ne-unit P 0<clk 1<po clock-min po∣clk g≡unit = ≤-impossible
  where
    open Presentation P

    -- 若 `g = unit`，则 `step y g = y`（`zeroʳ`）
    step-g-eq : ∀ y → step y g ≡ y
    step-g-eq y = trans (cong (step y) g≡unit) (zeroʳ y)

    -- `1` 是周期
    period-1 : Period (λ y → step y g) 1
    period-1 y = step-g-eq y

    -- `clock ∣ 1`
    clk∣1 : clock ∣ 1
    clk∣1 = clock-min 1 period-1

    -- `1 < clock`（由 ①③）
    1<clk : 1 < clock
    1<clk = ≤-trans 1<po (∣⇒≤ ⦃ <⇒NonZero 0<clk ⦄ po∣clk)

    -- `clock ≤ 1`
    clk≤1 : clock ≤ 1
    clk≤1 = ∣⇒≤ clk∣1

    -- 矛盾
    ≤-impossible : ⊥
    ≤-impossible = <⇒≱ 1<clk clk≤1
