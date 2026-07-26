{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.LinguisticsDiscrete
-- C58: 离散语言学 — GF(3) 三值语法 + Δ³≡0 递归截断
--
-- 核心命题:
--   1. 三值语法: 句法成分取 GF(3) 三态 (主语/谓语/宾语)
--   2. Δ³≡0 递归截断: 嵌套深度最多 3 层 (幂零性)
--
-- 0 postulate, 穷举法优先

module Sovereign.Applied.LinguisticsDiscrete where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.ProjectionDifferential
  using (GF3Func; Δ; Δ³≡0; Δ²-is-const; sum3)

--------------------------------------------------------------------------------
-- §1. GF(3) 三值语法
--
-- 经典语言学: 句法范畴是离散标签 (NP, VP, PP, ...)
-- 离散语言学: 句法成分取 GF(3) 三态
--   T₀ = 主语位 (吸收态: 接收动作)
--   T₁ = 谓语位 (平衡态: 传递动作)
--   T₂ = 宾语位 (表达态: 输出动作)
--
-- 句法叠加: ⊕ (GF(3) 加法)
-- 主语 + 宾语 = 归零 (T₁ ⊕ T₂ = T₀) — 论元结构闭合
--------------------------------------------------------------------------------

-- 三值句法范畴
SyntaxRole : Set
SyntaxRole = Trit

-- 论元结构闭合: 谓语 + 宾语 = 主语归零
argument-closure : T₁ ⊕ T₂ ≡ T₀
argument-closure = refl

-- 句法三重循环: 主→谓→宾→主 (特征 3)
syntax-cycle : ∀ (s : SyntaxRole) → (s ⊕ s) ⊕ s ≡ T₀
syntax-cycle T₀ = refl
syntax-cycle T₁ = refl
syntax-cycle T₂ = refl

--------------------------------------------------------------------------------
-- §2. Δ³≡0 递归截断: 嵌套深度最多 3 层
--
-- 连续语言学: 递归嵌入无上限 (Chomsky 递归性)
-- 离散语言学: Δ³≡0 → 三阶差分恒为零 → 嵌套最多 3 层
--
-- 物理证据: 人类工作记忆容量 ~4±1 (Miller 1956)
-- GF(3) 幂零性给出精确上界: 3 层
--------------------------------------------------------------------------------

-- 递归截断: 任意句法函数的三阶差分恒为零
recursion-truncation : ∀ (f : GF3Func) → Δ (Δ (Δ f)) ≡ (T₀ , T₀ , T₀)
recursion-truncation = Δ³≡0

-- 二阶差分坍缩为常数: 嵌套 2 层后结构固化
recursion-2-collapse : ∀ (f : GF3Func) →
  Δ (Δ f) ≡ (sum3 f , sum3 f , sum3 f)
recursion-2-collapse = Δ²-is-const
