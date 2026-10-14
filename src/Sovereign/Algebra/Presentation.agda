{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Presentation
-- 八要素统一类型类 —— 类型论展示群的标准接口（L3）
--
-- 正源: docs/duodecimal/11-type-theory-presentation.md §四「律算框架的群论公理」：
--   Group := 载体类型 (record)
--          + 生成元族 (data, 带代数来源标记)
--          + 关系族 (record 字段)
--          + 刚性作用 (Frobenius 从 GF9 诱导)
--          + 结构证明 (refl, 0 postulate)
--
-- 形状规范: docs/maps/八要素统一形状-2026-10-14.md §三（三段式）
-- 判据原文: docs/maps/M8-check-semantics.md:88「八要素齐备才有公理候选资格」
--
-- ═══════════════════════════════════════════════════════════════
-- 八要素对照（本文件即该形状的**类型类**实现）
-- ═══════════════════════════════════════════════════════════════
--  ① 载体      record Presentation (A : Set) 的**类型参数** A（非字段）
--  ② 生成元    field `step`（运算/作用）
--  ③ 关系      field `assoc` / `identityˡ` / `identityʳ`
--  ④ 相位      field `phase` + `phase-order` + `phase-cycle`
--  ⑤ 时钟      field `clock` + `clock-cycle`
--  ⑥ 归零      field `unit` + `zeroˡ` / `zeroʳ`
--  ⑦ 刚性      field `rigidity`（⚠ 约定：**必须从 GF9 的 galoisConjugate 诱导**，
--              不得在本层另立来源 —— 正源 §二 2.4「Frobenius 定义在 GF9 上」）
--  ⑧ 核对      field `check`（refl 层；正源：不产生结构）
--
-- ⚠ 两条硬约束（正源裁决，非本文件新立）：
--   1. 刚性**不得**定义在生成元层，须从 GF9 诱导（§二 2.4）
--   2. 核对是 refl 自洽确认、**不产生结构**（2026-09-08）
--   3. 八要素**不扩充**（2026-09-27）；壁垒/保真度命题不入本 record
--
-- 与既有结构的关系（不替代，只统一）：
--   - `UniversalAlgebra.Group` 等是**经典代数层级**（半群→群→环→域），
--     不含相位/时钟/刚性；本类型类是**展示群专用**，二者不同物（勿混）。
--   - `GroupTheory.ZeroOblivion` / `DayanCore` / `DCCyclicStructure` 是**具体件**的
--     关系 record；本类型类提供跨件统一接口（实例化即可对接）。

module Sovereign.Algebra.Presentation where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

--------------------------------------------------------------------------------
-- 迭代算子（相位/时钟的周期语句需要）
--------------------------------------------------------------------------------
iterate : {A : Set} → (A → A) → ℕ → A → A
iterate f zero    x = x
iterate f (suc n) x = f (iterate f n x)

--------------------------------------------------------------------------------
-- 八要素类型类
--------------------------------------------------------------------------------
record Presentation (A : Set) : Set₁ where
  field
    -- ② 生成元（运算/作用）
    step : A → A → A
    -- ⑥ 归零（单位元）
    unit : A
    -- ③ 关系（结合律 + 单位律）
    assoc     : ∀ x y z → step (step x y) z ≡ step x (step y z)
    zeroˡ     : ∀ x → step unit x ≡ x
    zeroʳ     : ∀ x → step x unit ≡ x
    -- ④ 相位（旋转算子 + 阶 + 循环语句）
    phase       : A → A
    phase-order : ℕ
    phase-cycle : ∀ x → iterate phase phase-order x ≡ x
    -- ⑤ 时钟（走钟周期 + 一圈回位语句）
    clock       : ℕ
    clock-cycle : ∀ x → iterate phase clock x ≡ x
    -- ⑦ 刚性（约定：必须由 GF9.galoisConjugate 诱导）
    rigidity : A → A
    -- ⑧ 核对（refl 层，仅确认定义自洽；正源：不产生结构）
    check : ∀ x → step x unit ≡ x

open Presentation public

--------------------------------------------------------------------------------
-- 实例：DuodecPoint 上的八要素展示结构（DC = C₃ × C₄）
--
-- 素材全部取自既有件（DuodecClock / DuodecClockProperties），本实例只做**对接**，
-- 不新证任何东西 —— 这正是 L3 的目的：把散在具体件里的八要素接到统一接口上。
--------------------------------------------------------------------------------
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (DuodecPoint; AlphaPower; a0; a1; a2; a3;
   mixedOp; duodec-e; mulAlpha; mixedOp-assoc; mixedOp-12-cycle;
   mixedOp-identityˡ; mixedOp-identityʳ; rho)
open import Sovereign.Algebra.GroupTheory.DuodecClockProperties using (alpha-order-4)

-- 相位算子：只作用相位分量（乘 α），损益分量不动
dc-phase : DuodecPoint → DuodecPoint
dc-phase (t , a) = (t , mulAlpha a1 a)

-- 相位四步回位（α⁴ = a0 ⟹ 乘 a1 四次 = 恒等）
-- AlphaPower 是 4 元素枚举、mulAlpha 为具体乘法表 ⇒ 逐例归一化即 refl
dc-phase-cycle : ∀ x → iterate dc-phase 4 x ≡ x
dc-phase-cycle (t , a0) = refl
dc-phase-cycle (t , a1) = refl
dc-phase-cycle (t , a2) = refl
dc-phase-cycle (t , a3) = refl

-- 时钟：相位分量走钟 12 步回位（12 = 3 × 4；相位侧按 4 归零，故 4 | 12 ⇒ 12 步 = id）
-- AlphaPower 是 4 元素枚举、mulAlpha 为具体乘法表 ⇒ 逐例归一化即 refl
dc-clock-cycle : ∀ x → iterate dc-phase 12 x ≡ x
dc-clock-cycle (t , a0) = refl
dc-clock-cycle (t , a1) = refl
dc-clock-cycle (t , a2) = refl
dc-clock-cycle (t , a3) = refl

dc-presentation : Presentation DuodecPoint
dc-presentation = record
  { step        = mixedOp
  ; unit        = duodec-e
  ; assoc       = mixedOp-assoc
  ; zeroˡ       = mixedOp-identityˡ
  ; zeroʳ       = mixedOp-identityʳ
  ; phase       = dc-phase
  ; phase-order = 4
  ; phase-cycle = dc-phase-cycle
  ; clock       = 12
  ; clock-cycle = dc-clock-cycle
  ; rigidity    = rho          -- 约定：由 GF9.galoisConjugate 诱导的相位反射
  ; check       = mixedOp-identityʳ
  }
