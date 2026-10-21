{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Analysis.DiscreteODE
--
-- 离散微分方程的最小基石：**齐次方程 `Δu = 0` 的解必为常数**（核是 1 维的）。
--
-- ## 数学背景
--
-- `GF3Func = Trit³` 上定义**循环差分**
--   `Δ (f₀ , f₁ , f₂) = (f₁ ⊖ f₀ , f₂ ⊖ f₁ , f₀ ⊖ f₂)`
-- （`⊖` = `⊕ negate`）。库内已有：
--   · `Δ³≡0`（三次差分恒零 ⇒ 每个函数都是「次数 ≤ 2 的离散多项式」）
--   · `Δ²-is-const`（二阶差分落在常数上）
--
-- 本模块补上**ODE 侧的结构定律**：`Δu = 0` 的解**唯一到常数**——
-- 即 `ker Δ` 恰是常函数集（3 个元素，维数 1）。
-- 连续统里这是「`u' = 0 ⇒ u` 常数」；这里没有极限，是 27 个情形的**纯组合**事实。
--
-- ## 与 `Foundation.CompletenessTheorem` 的关系
--
-- 该模块把 `ODEPDE` 的离散载体定为 `GF3Func`（「`Δ³≡0` 截断」），并指出
-- 缺的是**概念特有的结构定律**——**本模块补上的正是其中一条**（齐次解的唯一性）。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；27 情形穷举（有限论域，符合「≤27 case」纪律）
--   · 26 个非常数情形由 `()` 排除（等式在两具体项之间，无可合一构造子）
--------------------------------------------------------------------------------

module Sovereign.Synthesis.Analysis.DiscreteODE where

open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Analytic.ProjectionDifferential using (GF3Func; Δ)

zero3 : GF3Func
zero3 = T₀ , T₀ , T₀

--------------------------------------------------------------------------------
-- §1. ★★ 核 = 常数（齐次离散 ODE 的解唯一到常数）
--------------------------------------------------------------------------------

Δ-kernel-const : ∀ f → Δ f ≡ zero3 → Σ Trit (λ s → f ≡ (s , s , s))
Δ-kernel-const (T₀ , T₀ , T₀) refl = T₀ , refl
Δ-kernel-const (T₁ , T₁ , T₁) refl = T₁ , refl
Δ-kernel-const (T₂ , T₂ , T₂) refl = T₂ , refl
Δ-kernel-const (T₀ , T₀ , T₁) ()
Δ-kernel-const (T₀ , T₀ , T₂) ()
Δ-kernel-const (T₀ , T₁ , T₀) ()
Δ-kernel-const (T₀ , T₁ , T₁) ()
Δ-kernel-const (T₀ , T₁ , T₂) ()
Δ-kernel-const (T₀ , T₂ , T₀) ()
Δ-kernel-const (T₀ , T₂ , T₁) ()
Δ-kernel-const (T₀ , T₂ , T₂) ()
Δ-kernel-const (T₁ , T₀ , T₀) ()
Δ-kernel-const (T₁ , T₀ , T₁) ()
Δ-kernel-const (T₁ , T₀ , T₂) ()
Δ-kernel-const (T₁ , T₁ , T₀) ()
Δ-kernel-const (T₁ , T₁ , T₂) ()
Δ-kernel-const (T₁ , T₂ , T₀) ()
Δ-kernel-const (T₁ , T₂ , T₁) ()
Δ-kernel-const (T₁ , T₂ , T₂) ()
Δ-kernel-const (T₂ , T₀ , T₀) ()
Δ-kernel-const (T₂ , T₀ , T₁) ()
Δ-kernel-const (T₂ , T₀ , T₂) ()
Δ-kernel-const (T₂ , T₁ , T₀) ()
Δ-kernel-const (T₂ , T₁ , T₁) ()
Δ-kernel-const (T₂ , T₁ , T₂) ()
Δ-kernel-const (T₂ , T₂ , T₀) ()
Δ-kernel-const (T₂ , T₂ , T₁) ()

--------------------------------------------------------------------------------
-- §2. 计算验证
--------------------------------------------------------------------------------

-- 常函数都在核里（三个都 `refl`）
check-const₀ : Δ (T₀ , T₀ , T₀) ≡ zero3
check-const₀ = refl

check-const₁ : Δ (T₁ , T₁ , T₁) ≡ zero3
check-const₁ = refl

check-const₂ : Δ (T₂ , T₂ , T₂) ≡ zero3
check-const₂ = refl

-- 非常函数不在核里：`Δ (T₀,T₀,T₁) ≡ (T₀,T₁,T₂)` 与 `zero3` 不等
check-nonconst : Δ (T₀ , T₀ , T₁) ≡ (T₀ , T₁ , T₂)
check-nonconst = refl
