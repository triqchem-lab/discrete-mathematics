{-# OPTIONS --guardedness #-}

-- | Sovereign.Trust.TwoViewPlain — PGM P1「Plain 视图」：**无规则**（故意不开 --rewriting）
--
-- 本模块是 PGM P1（规则/定义解耦的两视图模拟）的对照臂之一：
--   · 生成元以**已定义函数**形态给出（`step`，三点 3-循环）
--   · 普遍定律**必须显式证明**（3 个 case）
--   · 本模块**不含任何 REWRITE 规则** ⇒ 消费方不应被迫开启 `--rewriting`
--
-- 为什么不 import 既有的 `PresentationGapBoundary`（那里也有 `Three`/`step`/`step-3-law`）：
--   那个模块头带 `{-# OPTIONS --rewriting #-}`，**import 它会强制消费方开旗标**
--   （实测 `[InfectiveImport]`），从而破坏本视图「无规则、免旗标」的对照意义。
--   ⇒ 这里的少量重复是**为对照实验服务的有意重复**，不是第二事实源（定理本体仍在
--   `PresentationGapBoundary`/`DuodecClock`；本模块只承载 P1 的对照臂）。

module Sovereign.Trust.TwoViewPlain where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- 已定义生成元（三点 3-循环）
--------------------------------------------------------------------------------

data Three : Set where
  p0 p1 p2 : Three

step : Three → Three
step p0 = p1
step p1 = p2
step p2 = p0

--------------------------------------------------------------------------------
-- Plain 视图：普遍定律要**显式证明**
--------------------------------------------------------------------------------

step-3-law : ∀ x → step (step (step x)) ≡ x
step-3-law p0 = refl
step-3-law p1 = refl
step-3-law p2 = refl

-- 对照：闭合实例由归一化器自己算（无需证明）
closed-instance : step (step (step p0)) ≡ p0
closed-instance = refl

--------------------------------------------------------------------------------
-- 抽象形态（与 DayanCore 同形）：关系必须**引用字段**
--------------------------------------------------------------------------------

record AbstractPresentation : Set₁ where
  field
    Carrier : Set
    δ : Carrier → Carrier
    δ³ : ∀ c → δ (δ (δ c)) ≡ c

open AbstractPresentation

-- 抽象形态下，定律只能由字段给出（没有规则可用）
from-field : (p : AbstractPresentation) (c : Carrier p) → δ p (δ p (δ p c)) ≡ c
from-field p c = δ³ p c

-- 0 postulate / 0 hole。
