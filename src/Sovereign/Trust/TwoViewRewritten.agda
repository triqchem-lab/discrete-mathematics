{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Trust.TwoViewRewritten — PGM P1「Rewritten 视图」：**带规则**
--
-- 本模块是 PGM P1 的另一臂：把展示关系声明为**作用域内**的规约规则，使普遍定律
-- 不再需要证明（`refl` 即可）。
--
-- ⚠ **编码前提（实测得出的硬约束）**：生成元必须**以 stuck 头部暴露**（此处用 postulate）
--   才可能建成 Rewritten 视图 —— Agda 拒收 **LHS 会归约**的规则
--   （`-W[no]RewriteLHSReduces`；见 `docs/techniques/pgm-assessment.md` §Q2 的 `Pgm1`/`Pgm2`：
--    生成元若是**已定义函数**，规则被拒 rc=42）。
--   ⇒ 所以「两视图」在今天的 Agda 上**只能对抽象展示群（生成元为符号）建立**。
--
-- ⚠ **代价**：本模块携带规则 ⇒ 任何 import 它的模块**被迫**开启 `--rewriting`
--   （实测 `[InfectiveImport]`），且**无法只取定义、不要规则**（见 PGM 评估 §Q1）。
--
-- ⚠ **postulate 性质声明**：此处的 `Carrier`/`δ` 是**抽象展示群的签名**、`δ³-law` 是其**关系**
--   （即条件命题的**前件**），**不是"未证的引理"**。它们不冒充定理。

module Sovereign.Trust.TwoViewRewritten where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

--------------------------------------------------------------------------------
-- 抽象展示群：生成元与关系以 postulate（stuck 头部）暴露
--------------------------------------------------------------------------------

postulate
  Carrier : Set
  δ : Carrier → Carrier
  δ³-law : ∀ c → δ (δ (δ c)) ≡ c

{-# REWRITE δ³-law #-}

--------------------------------------------------------------------------------
-- L2 用法：普遍定律**不需要证明**
--------------------------------------------------------------------------------

law-auto : ∀ c → δ (δ (δ c)) ≡ c
law-auto = λ c → refl

-- 注：这条 `refl` 在**没有**上面的 REWRITE 时写不出来（对照臂见 `TwoViewPlain`：
--     那边必须 3 个 case 显式证明；差异由 P1 的三个消费方探针用 exit 码量出）。
