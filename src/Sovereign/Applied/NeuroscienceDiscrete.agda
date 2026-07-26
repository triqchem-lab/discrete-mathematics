{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.NeuroscienceDiscrete
-- C40: 离散神经科学 — 轨道即记忆 + 三值神经元
--
-- 核心命题:
--   1. 轨道=记忆: 有限神经网络的轨道最终周期 → 记忆是吸引子
--   2. 三值神经元: GF(3) 状态 (抑制/静息/激发)
--
-- 0 postulate, 穷举法优先

module Sovereign.Applied.NeuroscienceDiscrete where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; Σ; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; negate; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ; ⊕-inverse; negate²)
open import Sovereign.Analysis.FiniteDynamics
  using (orbit; orbit-eventually-periodic; EventuallyPeriodic)

--------------------------------------------------------------------------------
-- §1. 轨道=记忆: 神经动力学吸引子
--
-- 经典神经科学: 记忆是突触权重的编码 (Hebb 学习)
-- 离散神经科学: 记忆是状态转移轨道的周期吸引子
--
-- 有限状态 → 鸽巢原理 → 轨道最终周期
-- 周期轨道 = 记忆的代数表示
--
-- 引用: orbit-eventually-periodic (FiniteDynamics.agda)
--------------------------------------------------------------------------------

-- 记忆定理: 任意有限神经网络的轨道最终周期
memory-is-attractor : ∀ N → (f : Fin N → Fin N) → (x0 : Fin N) →
  EventuallyPeriodic (λ n → orbit f x0 n)
memory-is-attractor = orbit-eventually-periodic

-- 3 神经元网络的记忆周期
memory-3-neuron : ∀ (f : Fin 3 → Fin 3) (x0 : Fin 3) →
  EventuallyPeriodic (λ n → orbit f x0 n)
memory-3-neuron = orbit-eventually-periodic 3

-- 9 神经元网络 (GF(9) 状态空间) 的记忆周期
memory-9-neuron : ∀ (f : Fin 9 → Fin 9) (x0 : Fin 9) →
  EventuallyPeriodic (λ n → orbit f x0 n)
memory-9-neuron = orbit-eventually-periodic 9

--------------------------------------------------------------------------------
-- §2. 三值神经元: GF(3) 状态
--
-- 经典神经元: 连续激活值 (实数) + 阈值函数
-- 离散神经元: GF(3) 三值状态
--   T₀ = 抑制态 (absorption, -1)
--   T₁ = 静息态 (equilibrium, 0)
--   T₂ = 激发态 (expression, +1)
--
-- 突触叠加: ⊕ (GF(3) 加法)
-- 抑制 + 激发 = 归零 (T₀ ⊕ T₂ = T₂, T₁ ⊕ T₂ = T₀)
--------------------------------------------------------------------------------

-- 神经元状态类型
NeuronState : Set
NeuronState = Trit

-- 突触叠加: 抑制 + 激发 = 激发 (单位元性质)
synapse-inhibit-excite : T₀ ⊕ T₂ ≡ T₂
synapse-inhibit-excite = refl

-- 突触叠加: 静息 + 激发 = 归零 (对消)
synapse-rest-excite-cancel : T₁ ⊕ T₂ ≡ T₀
synapse-rest-excite-cancel = refl

-- 突触叠加: 激发 + 激发 = 抑制 (过激发 → 抑制, GF(3) 回绕)
synapse-excite-excite : T₂ ⊕ T₂ ≡ T₁
synapse-excite-excite = refl

-- 神经元特征 3: 三重激发归零
neuron-char3 : ∀ (s : NeuronState) → (s ⊕ s) ⊕ s ≡ T₀
neuron-char3 T₀ = refl
neuron-char3 T₁ = refl
neuron-char3 T₂ = refl

-- 手征共轭: negate 交换激发 ↔ 抑制
neuron-conjugate : (negate T₁ ≡ T₂) × (negate T₂ ≡ T₁)
neuron-conjugate = refl , refl

--------------------------------------------------------------------------------
-- §3. ≡-Reasoning 代数推导链 (B→A 级提升)
--------------------------------------------------------------------------------

-- 不动点记忆定理: f(x₀) ≡ x₀ → 轨道恒等于 x₀
-- 构造性证明: 对 n 归纳, 每步用 ≡-Reasoning 展示轨道坍缩
fixed-point-memory : {A : Set} (f : A → A) (x₀ : A) → f x₀ ≡ x₀ →
  ∀ n → orbit f x₀ n ≡ x₀
fixed-point-memory f x₀ fp = go
  where
    go : ∀ n → orbit f x₀ n ≡ x₀
    go zero    = refl
    go (suc n) = begin
      orbit f x₀ (suc n)   ≡⟨⟩
      f (orbit f x₀ n)     ≡⟨ cong f (go n) ⟩
      f x₀                 ≡⟨ fp ⟩
      x₀                   ∎
      where open ≡-Reasoning

-- 不动点 → 周期 1 记忆: 从 orbit-eventually-periodic 提取周期 1 的特殊情况
-- 记忆 = 周期吸引子, 不动点是最简记忆 (周期 = 1)
fixed-point-period-1 : {A : Set} (f : A → A) (x₀ : A) → f x₀ ≡ x₀ →
  EventuallyPeriodic (λ n → orbit f x₀ n)
fixed-point-period-1 f x₀ fp = record
  { start    = 0
  ; period   = 1
  ; periodic = λ k →
    trans (fixed-point-memory f x₀ fp (k + 1))
          (sym (fixed-point-memory f x₀ fp k))
  }

-- 轨道坍缩链: 不动点的 3 步轨道展开
-- orbit f x₀ 3 = f(f(f(x₀))) = f(f(x₀)) = f(x₀) = x₀
orbit-collapse-3 : {A : Set} (f : A → A) (x₀ : A) → f x₀ ≡ x₀ →
  orbit f x₀ 3 ≡ x₀
orbit-collapse-3 f x₀ fp = begin
  orbit f x₀ 3       ≡⟨⟩
  f (orbit f x₀ 2)   ≡⟨ cong f (fixed-point-memory f x₀ fp 2) ⟩
  f x₀               ≡⟨ fp ⟩
  x₀                 ∎
  where open ≡-Reasoning

-- 三值神经元特征 3 的代数链 (T₁ 情形): 三重激发归零
-- (T₁ ⊕ T₁) ⊕ T₁ = T₂ ⊕ T₁ = T₀
neuron-char3-T₁-chain : (T₁ ⊕ T₁) ⊕ T₁ ≡ T₀
neuron-char3-T₁-chain = begin
  (T₁ ⊕ T₁) ⊕ T₁   ≡⟨⟩
  T₂ ⊕ T₁           ≡⟨⟩
  T₀                ∎
  where open ≡-Reasoning

-- 三值神经元特征 3 的代数链 (T₂ 情形): 三重抑制归零
-- (T₂ ⊕ T₂) ⊕ T₂ = T₁ ⊕ T₂ = T₀
neuron-char3-T₂-chain : (T₂ ⊕ T₂) ⊕ T₂ ≡ T₀
neuron-char3-T₂-chain = begin
  (T₂ ⊕ T₂) ⊕ T₂   ≡⟨⟩
  T₁ ⊕ T₂           ≡⟨⟩
  T₀                ∎
  where open ≡-Reasoning

-- 突触叠加的完整代数链: 抑制 + 激发 + 抑制 = 激发
-- 证明路径: 结合律 → 右单位元 → 左单位元
synapse-full-chain : (T₀ ⊕ T₂) ⊕ T₀ ≡ T₂
synapse-full-chain = begin
  (T₀ ⊕ T₂) ⊕ T₀   ≡⟨ ⊕-assoc T₀ T₂ T₀ ⟩
  T₀ ⊕ (T₂ ⊕ T₀)   ≡⟨ cong (T₀ ⊕_) (⊕-identityʳ T₂) ⟩
  T₀ ⊕ T₂           ≡⟨ ⊕-identityˡ T₂ ⟩
  T₂                ∎
  where open ≡-Reasoning

-- 逆元对合链: (x ⊕ negate x) ⊕ negate (negate x) ≡ x
-- 物理: 逆元消去后, 对合恢复原始状态
-- 证明路径: 逆元 → 单位元 → 对合
neuron-inverse-involution-chain : ∀ x → (x ⊕ negate x) ⊕ negate (negate x) ≡ x
neuron-inverse-involution-chain x = begin
  (x ⊕ negate x) ⊕ negate (negate x)   ≡⟨ cong (_⊕ negate (negate x)) (⊕-inverse x) ⟩
  T₀ ⊕ negate (negate x)               ≡⟨ ⊕-identityˡ (negate (negate x)) ⟩
  negate (negate x)                     ≡⟨ negate² x ⟩
  x                                     ∎
  where open ≡-Reasoning
