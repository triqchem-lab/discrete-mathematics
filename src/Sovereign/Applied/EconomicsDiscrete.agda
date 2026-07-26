{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.EconomicsDiscrete
-- C57: 离散经济学 — 有限资源分配均衡 + 729 格点鸽巢原理
--
-- 核心命题:
--   1. 均衡存在: 729 格点上的确定性资源分配 → 轨道最终周期 (鸽巢原理)
--   2. 分配归零: GF(3) 特征 3 → 三重分配回归均衡
--
-- 0 postulate, 穷举法优先

module Sovereign.Applied.EconomicsDiscrete where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_)
open import Data.Fin using (Fin; toℕ)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Analysis.FiniteDynamics
  using (orbit; orbit-eventually-periodic; EventuallyPeriodic; pigeonhole-fin)

--------------------------------------------------------------------------------
-- §1. 均衡存在性: 729 格点上的资源分配
--
-- 经典经济学: 一般均衡存在性需要 Brouwer/Kakutani 不动点定理 (非构造性)
-- 离散经济学: T⁶ = GF(3)⁶ 有 729 个格点, 确定性分配 → 鸽巢原理 → 均衡
--
-- 分配函数 f : Fin 729 → Fin 729 是确定性映射
-- 729 个状态 → 轨道最终周期 → 均衡存在 (构造性证明)
--------------------------------------------------------------------------------

-- 729 格点均衡存在: 任意分配函数的轨道最终周期
equilibrium-729 : ∀ (f : Fin 729 → Fin 729) (x0 : Fin 729) →
  EventuallyPeriodic (λ n → orbit f x0 n)
equilibrium-729 = orbit-eventually-periodic 729

-- 鸽巢碰撞: 730 个分配结果中必有重复 → 均衡的构造性证据
allocation-pigeonhole : ∀ (f : Fin 730 → Fin 729) →
  Σ (Fin 730) (λ i → Σ (Fin 730) (λ j → toℕ i < toℕ j × f i ≡ f j))
allocation-pigeonhole = pigeonhole-fin 729

--------------------------------------------------------------------------------
-- §2. GF(3) 分配归零
--
-- 资源三态: T₀(匮乏)/T₁(均衡)/T₂(过剩)
-- 特征 3: 同一资源三重分配后归零 → 周期性均衡
--------------------------------------------------------------------------------

-- 三重分配归零: x ⊕ x ⊕ x ≡ T₀
triple-allocation-zero : ∀ (r : Trit) → (r ⊕ r) ⊕ r ≡ T₀
triple-allocation-zero T₀ = refl
triple-allocation-zero T₁ = refl
triple-allocation-zero T₂ = refl

-- 匮乏 + 过剩 = 归零 (供需对冲)
supply-demand-cancel : T₁ ⊕ T₂ ≡ T₀
supply-demand-cancel = refl
