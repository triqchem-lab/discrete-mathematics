{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi1dWindMod3
--
-- **C3-b（人类 2026-10-21 裁决）**：`π₁ᵈ(T¹) ↠ C₃`，**标注截断②**
--
-- ## 裁决原文
--
-- > **C3-b 立即做**（`π₁ᵈ(T¹) ↠ C₃`，标注截断②）……**这是对 `π₁ᵈ` 的精确刻画**
-- > ——它是投影，不是本源，净位移 mod 3 是非忠实商（违反 L0 红线），但这是截断②的读数，合法。
-- >
-- > **裁决 2 第 3 步作废**：它假设「三步归零 ⇒ `π₁ᵈ ≅ C₃`」，但实际 `AHomotopy` 在 Cayley 图上
-- > 不塌缩（无三角形），所以 `π₁ᵈ(T¹)` 有无穷多个元素。
--
-- ## ⚠ 一个必须写清的数学细节
--
-- 裁决说「净位移 = **圈数** mod 3」。**不能**用**走长** mod 3：
-- `T6CayleyVec 1` 的闭走长度**恒为 3 的倍数** ⇒ `走长 mod 3 ≡ 0` 恒成立 ⇒ 那是**常值**映射 ✗
-- 非平凡的是**圈数**（= 走长 / 3）mod 3 ✓
--
-- 本模块在**圈数层**（即 ℕ）给出这条投影，并用已证的 `cycpow-injective`
-- （ℕ ↪ `π₁ᵈ`）把它接到 `π₁ᵈ` 上：
--
-- ```
--   ℕ ──windN──↠ C₃            （满射、非单射）
--   ℕ ──cycpow──↪ π₁ᵈ(T¹)      （cycpow-injective：不同圈数不同类）
--   ⇒ π₁ᵈ(T¹) 上有一个满射到 C₃ 的读数，且它**丢掉圈数** ⇒ 截断②
-- ```
--
-- **被丢掉的正是圈数本身**：`cycpow 0` 与 `cycpow 3` 是**不同**的类（`cycpow-injective`），
-- 但投影到 C₃ 后**同一个像** ⇒ 非忠实商 ✓ 这正是 `00-definition-start-point.md:19`
-- 所说的 `C₄→C₂` 同类错误（这里是 `ℕ→C₃`）。
--
-- ## 本模块**不**声称的
--
--   · **不**声称 `π₁ᵈ(T¹) ≅ C₃` ✗ —— `cycpow-injective` / `cyc3≢nil` / `no-collapse-N`
--     三条内核事实共同否定它（裁决 2 第 3 步已作废）。
--   · **不**在 `AHomotopy`-商上直接定义 `wind` —— 那需要「每个闭走都是某 `cycpow n`」
--     的满射定理（尚未证）；本模块改走「ℕ ↪ π₁ᵈ」这条已证的通道 ✓
--   · **不**涉及 `AStepStd` 口径（那是 C3-a，**新对象** `π₁ᵈˢᵗᵈ`，另行处理）✗
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `Pi1dCycleThree` 的 `cycpow` / `cycpow-injective`（不重证）

module Sovereign.Synthesis.Homotopy.Pi1dWindMod3 where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Empty using (⊥)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import Sovereign.Synthesis.Homotopy.T6CayleyGraph using (succF3)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (AHomotopy)
open import Sovereign.Synthesis.Homotopy.Pi1dCycleThree
  using (G3; cycpow; cycpow-injective; cycpow-0≢3)

--------------------------------------------------------------------------------
-- §1. 圈数 mod 3（用 `succF3` 递归定义，**不需要除法**）
--------------------------------------------------------------------------------

windN : ℕ → Fin 3
windN zero    = Fin.zero
windN (suc n) = succF3 (windN n)

-- 三个值都取到（定义性）
windN-0 : windN 0 ≡ Fin.zero
windN-0 = refl
windN-1 : windN 1 ≡ Fin.suc Fin.zero
windN-1 = refl
windN-2 : windN 2 ≡ Fin.suc (Fin.suc Fin.zero)
windN-2 = refl
windN-3 : windN 3 ≡ Fin.zero
windN-3 = refl

-- ★ 满射
windN-surj : ∀ (c : Fin 3) → ∃ (λ (n : ℕ) → windN n ≡ c)
windN-surj Fin.zero                     = 0 , refl
windN-surj (Fin.suc Fin.zero)           = 1 , refl
windN-surj (Fin.suc (Fin.suc Fin.zero)) = 2 , refl

-- 周期性：`windN (n + 3) ≡ windN n`
windN-period : ∀ n → windN (n + 3) ≡ windN n
windN-period zero    = refl
windN-period (suc n) = cong succF3 (windN-period n)

--------------------------------------------------------------------------------
-- §2. ★ 非单射：0 与 3 同像但不同圈数
--------------------------------------------------------------------------------

0≢3 : 0 ≢ 3
0≢3 ()

windN-not-inj : ¬ (∀ m n → windN m ≡ windN n → m ≡ n)
windN-not-inj inj = 0≢3 (inj 0 3 refl)

--------------------------------------------------------------------------------
-- §3. ★★ 接到 π₁ᵈ：不同类、同一投影像 ⇒ 投影丢圈数（截断②）
--------------------------------------------------------------------------------

-- `cycpow 0` 与 `cycpow 3` 是**不同**的同伦类（直接复用 Pi1dCycleThree 已证的 cycpow-0≢3 ✓）

-- 但它们的**圈数投影像相同**
wind-collapse : windN 0 ≡ windN 3
wind-collapse = refl

-- ★★ 合起来：这条投影**丢掉圈数** ⇒ 非忠实商 ⇒ 截断②（合法，但必须标注）
wind-loses-laps :
    (windN 0 ≡ windN 3)
  × (¬ (AHomotopy G3 (cycpow 0) (cycpow 3)))
wind-loses-laps = wind-collapse , cycpow-0≢3
