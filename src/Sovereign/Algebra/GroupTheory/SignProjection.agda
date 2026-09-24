{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.SignProjection
-- 符号投影 C₄ → C₂：投影层「1 = −1」伪矛盾的形式化 + 跨层非忠实定理
--
-- ── 层级口径（2026-09-24 用户裁定）────────────────────────────────────────
--   **本源层**: ⟨α⟩ = C₄（相位, `AlphaPower`）—— 展示群生成方式给出的结构。
--   **投影层**: `Sign` = C₂（符号, ±1）—— C₄ 的**非忠实商**, 核 = ⟨α²⟩ = {a0, a2}。
--
--   ⚠ 关键（跨层不可比）: 外部工作（如 λ : ℕ → {±1}）**全在投影层**。
--   他们导出的「1 = −1」是**投影层的伪矛盾** —— 它在 Sign 里**真的成立**
--   （`sign-collapses`）, 而本源层 `a2 ≢ a0` 从不塌。两个层里的同名陈述
--   **不构成矛盾、也不是同构**（同构要求同一层；跨层只能谈「投影是否保结构」）。
--
-- ── 本模块三件套 ─────────────────────────────────────────────────────────
--   §1 `sign-hom`          : sign 是群同态（**投影函子**的合法性, 16 case）
--   §2 `sign-collapses`    : **投影层里 1 = −1**（sign a0 ≡ sign a2, refl）
--        对照 `source-one-ne-neg-one` : 本源层 a2 ≢ a0（空模式）
--   §3 `sign-not-faithful` : **跨层壁垒** —— sign 非单射（a2 与 a0 同像）
--        ⇒ 任何在 Sign 内的推导**不触及** C₄ 结构
--
--   与 `ABCL1.no-injective-hom` 的关系: **同族不同目标** —— 后者证「不存在
--   保单位单射同态 ⟨α⟩ → V₄」（R₁₂ 单位群, 指数 2）, 本模块证「符号投影
--   ⟨α⟩ → C₂ 不忠实」。二者同属断言族「**本源 → 投影不保结构**」。
--
-- ⚠ 诚实边界（原创性, 随引用一起）: 数学内核「C₄ 到 C₂/V₄ 不存在保结构单射」
--   是**标准有限群论**（阶数障碍: C₄ 有 4 阶元, C₂/V₄ 指数 ≤ 2）。
--   本模块的贡献是把它形式化为**可复用的投影判据**并放进「本源/投影」分层框架
--   ——**不声称新的群论事实**。
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.GroupTheory.SignProjection where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (AlphaPower; a0; a1; a2; a3; mulAlpha)

--------------------------------------------------------------------------------
-- §0. 投影目标: 符号群 C₂（奇偶指数）
--------------------------------------------------------------------------------

data Sign : Set where
  s+ : Sign        -- 偶指数: {a0 = 1, a2 = −1} —— 核的陪集主像
  s- : Sign        -- 奇指数: {a1 = α, a3 = α³}

_⊗ˢ_ : Sign → Sign → Sign
s+ ⊗ˢ y  = y
s- ⊗ˢ s+ = s-
s- ⊗ˢ s- = s+

sign : AlphaPower → Sign
sign a0 = s+
sign a1 = s-
sign a2 = s+
sign a3 = s-

--------------------------------------------------------------------------------
-- §1. sign 是群同态 —— 「投影函子」的合法性（16 case, 恰在穷举法上限内）
--------------------------------------------------------------------------------

sign-hom : ∀ (x y : AlphaPower) → sign (mulAlpha x y) ≡ sign x ⊗ˢ sign y
sign-hom a0 a0 = refl
sign-hom a0 a1 = refl
sign-hom a0 a2 = refl
sign-hom a0 a3 = refl
sign-hom a1 a0 = refl
sign-hom a1 a1 = refl
sign-hom a1 a2 = refl
sign-hom a1 a3 = refl
sign-hom a2 a0 = refl
sign-hom a2 a1 = refl
sign-hom a2 a2 = refl
sign-hom a2 a3 = refl
sign-hom a3 a0 = refl
sign-hom a3 a1 = refl
sign-hom a3 a2 = refl
sign-hom a3 a3 = refl

--------------------------------------------------------------------------------
-- §2. 投影层的「1 = −1」—— 伪矛盾的栖身地
--
-- 外部导出的「1 = −1」在 Sign 里**真的成立**: 1 与 −1 同像（核 = {a0, a2}）。
-- 但本源层不塌 —— 两个陈述**同名不同层**, 谁也不反驳谁。
--------------------------------------------------------------------------------

-- 投影层: 「1 与 −1 不可分」
sign-collapses : sign a0 ≡ sign a2
sign-collapses = refl

-- 本源层对照: 1 ≠ −1（空模式可证, 与 ABCL1.a2≢a0 同型）
source-one-ne-neg-one : a2 ≢ a0
source-one-ne-neg-one ()

--------------------------------------------------------------------------------
-- §3. 跨层壁垒: 投影不忠实
--
-- 核 = ⟨α²⟩ = {a0, a2} 非平凡 ⇒ sign 不是单射 ⇒
-- **任何在投影层内的推导都不触及本源结构**（C₄ 的 4 阶信息在 Sign 中不存在）。
-- 这是「本源 → 投影」的**跨层定理**, 不是投影层内的现象。
--------------------------------------------------------------------------------

sign-not-faithful : ¬ (∀ x y → sign x ≡ sign y → x ≡ y)
sign-not-faithful inj = source-one-ne-neg-one (inj a2 a0 refl)

--------------------------------------------------------------------------------
-- §4. 诚实边界（重申）
--
-- ✓ 已证: §1 同态性 / §2 双层对照 / §3 非忠实（全部 refl 或空模式）。
-- ✗ 不声称:
--   ① 新的群论事实 —— 阶数障碍是标准内容;
--   ② 对外部定理的反驳 —— 外部工作在投影层且自洽, 本模块只裁定**层级**;
--   ③ 「同构」类比 —— 跨层的两个对象不能叫同构（用户裁定）。
--------------------------------------------------------------------------------
