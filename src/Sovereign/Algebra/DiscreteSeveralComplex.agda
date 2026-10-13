{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DiscreteSeveralComplex
-- DiscreteSeveralComplex — 离散多复变 (MSC 32)
-- ℂⁿ 被诊断 TypeError: 全纯域不可有限编码
-- 离散替代: GF(3)ⁿ 函数空间 + 有限复形 Cauchy-Riemann
-- 0 postulate.

-- | 离散多复变实例核
--
-- 核心原则：离散多复变实例核——离散基座实例核（非一般定理，诚实边界随引用）
--          穷举/归纳边界遵守（≤27 case 或具名链，trans ≤3）
--          代数污染禁令（禁 Float/Double/超越函数）
--
-- 包含：∂̄f、not-hol-xy、hol-const
--
-- 【2026-10-11 内容分级注记】§1 的 not-hol-xy / hol-const 为**点核对件**（refl 数值点，非定理——
--   勿挂定理名）；⚠ **statement_wrong 疑点待裁决**：hol-const 注释称「⚠ 勘正（2026-10-11）：本模块 ∂̄f 为简化差分形（无减项）**非 CR 算子**——hol-const 点核对件实测 ∂̄f(常值)=T₂≢0；「常函数全纯」的直觉对应需真 ∂̄ 算子（待设计，立界）——本件为点核对件非定理」而其证明值
--   ∂̄f(常值)=T₂≢0——张力根源疑为 ∂̄f 定义非差分算子（f(x⊕1)y ⊕ f x(y⊕1) 无相减项）；
--   数学面不动，待裁决后修（本注记仅如实标注）。本模块零代码消费者（grep 实证 2026-10-11）。

module Sovereign.Algebra.DiscreteSeveralComplex where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

-- §1. GF(3)² 上的多重复形 ----------------------------------------
-- 离散 Cauchy-Riemann 算子: ∂̄f = ∂f/∂x ⊕ i·∂f/∂y
-- 在 GF(3): i = T₂ (因为 T₂⊗T₂ = T₁ = -1)
∂̄f : (Trit → Trit → Trit) → Trit → Trit → Trit
∂̄f f x y = f (x ⊕ T₁) y ⊕ f x (y ⊕ T₁)

-- 整函数 (全纯): ∂̄f = 0
-- f(x,y) = x ⊕ y: ∂̄f = Δf ≠ 0 → 非全纯
not-hol-xy : ∂̄f (λ x y → x ⊕ y) T₀ T₀ ≡ T₂
not-hol-xy = refl  -- f(1,0)⊕f(0,1) = 1⊕1 = 2 = T₂

-- ⚠ 勘正（2026-10-11）：本模块 ∂̄f 为简化差分形（无减项）**非 CR 算子**——hol-const 点核对件实测 ∂̄f(常值)=T₂≢0；「常函数全纯」的直觉对应需真 ∂̄ 算子（待设计，立界）——本件为点核对件非定理
hol-const : ∂̄f (λ x y → T₁) T₀ T₀ ≡ T₂
hol-const = refl

-- §2. Hartogs 现象离散版 ----------------------------------------
-- GF(3)² 上所有函数自动解析延拓 (拉格朗日插值)
-- 无"孤立奇点"概念 — 有限集上的函数天然全局定义.
-- 0 postulate.
