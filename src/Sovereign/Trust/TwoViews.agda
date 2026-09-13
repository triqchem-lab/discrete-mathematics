{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Trust.TwoViews — PGM P1「两视图」对照锚点
--
-- 数学背景（展示群第一原理）：一个展示群 = ⟨生成元 | 关系⟩。同一个关系可以有两种存在方式——
--   * **只作为定义性质**：下游要显式证明；
--   * **作为定向重写规则**：下游 `refl` 自动归约。
-- 本模块同时 import 同一展示群的两套视图，把这一对照固定成一个可编译的事实：
--
--   * `Sovereign.Trust.TwoViewPlain`     —— 只有定义，故意不带规则；
--   * `Sovereign.Trust.TwoViewRewritten` —— 定义 + `{-# REWRITE δ³-law #-}`。
--
-- 核心原则（P1 实测，证据见 dype `docs/theory/PGM-metatheory-and-plan.md` §4）：
--   ① 定义式视图的下游**零旗标成本**；而本模块只要 import 了带规则的一侧，
--      Agda 的传染性检查就强制本模块自带 `--rewriting`（去掉它即 `[InfectiveImport]` rc=42）；
--   ② 规则式视图让**任意点**上的三阶律由 `refl` 闭合；定义式视图只对**具体实例**定义归约成立，
--      任意点必须显式证明（三条 case）。
--
-- ⚠ 本模块是**机制对照**，不是关于 DC 真实 δ 的定理：两侧的 `Three`/`step` 都是最小模型，
--   规则式一侧的生成元以 postulate 给出（stuck 头才能承载合法 REWRITE 规则）。
module Sovereign.Trust.TwoViews where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

import Sovereign.Trust.TwoViewPlain as Plain
open import Sovereign.Trust.TwoViewPlain using (Three; p0; step)

import Sovereign.Trust.TwoViewRewritten as Rew
open import Sovereign.Trust.TwoViewRewritten using (Carrier; δ; law-auto)

------------------------------------------------------------------------
-- 规则式一侧
------------------------------------------------------------------------

-- 任意点：规则跨模块生效 ⇒ `refl` 即可闭合（无需 case 分析）
rewritten-general : ∀ c → δ (δ (δ c)) ≡ c
rewritten-general = law-auto

------------------------------------------------------------------------
-- 定义式一侧
------------------------------------------------------------------------

-- 具体实例：定义归约照常发生 ⇒ `refl` 也可闭合
plain-instance : step (step (step p0)) ≡ p0
plain-instance = refl

-- 任意点：没有规则 ⇒ 必须显式给出三条 case 的证明
plain-general : ∀ x → step (step (step x)) ≡ x
plain-general = Plain.step-3-law
