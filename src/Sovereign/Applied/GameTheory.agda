{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.GameTheory
-- C38: 离散博弈论 — 鸽巢原理 → 周期轨道存在 + GF(3) 三值策略
--
-- 核心命题:
--   1. 周期轨道存在: 有限策略空间 → 鸽巢原理 → 轨道最终周期
--   2. 不动点实例: 恒等函数/常数函数有不动点 (具体构造)
--   3. GF(3) 三值策略: T₀(合作)/T₁(中立)/T₂(对抗), 3 case 穷举
--
-- 重要区分:
--   纯策略 Nash 均衡 (不动点) 不一定存在!
--   例: f(0)=1, f(1)=0 在 Fin 2 上没有不动点。
--   经典 Nash 存在性定理需要混合策略 (概率分布) + Brouwer 不动点定理。
--   离散博弈论的正确替代: 所有有限博弈都有周期轨道 (鸽巢原理, 构造性)。
--
-- 0 postulate, 穷举法优先

module Sovereign.Applied.GameTheory where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_)
open import Data.Fin using (Fin; toℕ)
  renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Analysis.FiniteDynamics
  using (orbit; pigeonhole-fin; orbit-eventually-periodic; EventuallyPeriodic)

--------------------------------------------------------------------------------
-- §1. 周期轨道存在性: 鸽巢原理 → 轨道最终周期
--
-- 经典博弈论: Nash 均衡存在性需要 Brouwer 不动点定理 (非构造性)
--   且仅对混合策略 (概率分布) 成立。
-- 纯策略 Nash 均衡 = 不动点 f(x) = x, 不一定存在:
--   反例: f : Fin 2 → Fin 2, f(0) = 1, f(1) = 0 没有不动点。
--
-- 离散博弈论的正确定理:
--   有限策略空间 + 确定性更新 → 鸽巢原理 → 轨道最终周期
--   这是构造性的, 不需要 Brouwer 不动点定理。
--   周期轨道是 Nash 均衡在离散设定下的正确替代概念。
--------------------------------------------------------------------------------

-- 周期轨道存在: 任意有限策略空间上的确定性更新必有周期轨道
-- 注意: 这不是 "Nash 均衡存在" — 纯策略 Nash 均衡 (不动点) 不一定存在
orbit-periodic-exists : ∀ N → (f : Fin N → Fin N) → (x0 : Fin N) →
  EventuallyPeriodic (λ n → orbit f x0 n)
orbit-periodic-exists = orbit-eventually-periodic

-- 3 策略周期轨道 (GF(3) 策略空间)
orbit-periodic-3-strategy : ∀ (f : Fin 3 → Fin 3) (x0 : Fin 3) →
  EventuallyPeriodic (λ n → orbit f x0 n)
orbit-periodic-3-strategy = orbit-eventually-periodic 3

-- 鸽巢碰撞: N+1 个策略中必有重复 → 周期轨道的构造性证据
orbit-pigeonhole : ∀ n → (f : Fin (suc n) → Fin n) →
  Σ (Fin (suc n)) (λ i → Σ (Fin (suc n)) (λ j → (toℕ i < toℕ j) × (f i ≡ f j)))
orbit-pigeonhole = pigeonhole-fin

--------------------------------------------------------------------------------
-- §1b. 不动点存在的具体实例
--
-- 并非所有 f : Fin N → Fin N 都有不动点 (见上方反例)。
-- 但特定类型的函数确实有不动点, 以下是构造性证明:
--------------------------------------------------------------------------------

-- 恒等函数: 每个点都是不动点
nash-identity : ∀ (x : Fin 3) → (λ (y : Fin 3) → y) x ≡ x
nash-identity x = refl

-- 常数函数: 常数本身是不动点
nash-constant : let f : Fin 3 → Fin 3; f = λ _ → fzero in f fzero ≡ fzero
nash-constant = refl

-- 常数函数 (一般化): 对任意 c : Fin N, 常函数 f(x)=c 在 x=c 处有不动点
nash-constant-general : ∀ N → (c : Fin N) → (λ (_ : Fin N) → c) c ≡ c
nash-constant-general N c = refl

--------------------------------------------------------------------------------
-- §2. GF(3) 三值策略
--
-- 经典博弈论: 策略通常是连续的 (混合策略 = 概率分布)
-- 离散博弈论: 策略是 GF(3) 三值的
--   T₀ = 合作 (吸收态)
--   T₁ = 中立 (平衡态)
--   T₂ = 对抗 (表达态)
--
-- 策略叠加: ⊕ (GF(3) 加法)
-- 合作 + 对抗 = 归零 (T₁ ⊕ T₂ = T₀) — 对立策略相消
--------------------------------------------------------------------------------

-- 三值策略类型
Strategy : Set
Strategy = Trit

-- 策略叠加归零: 合作 + 对抗 = 中立归零
strategy-annihilation : T₁ ⊕ T₂ ≡ T₀
strategy-annihilation = refl

-- 策略叠加表 (3×3 = 9 case, 全部 refl)
strategy-sum-coop-coop : T₀ ⊕ T₀ ≡ T₀ ; strategy-sum-coop-coop = refl
strategy-sum-coop-neut : T₀ ⊕ T₁ ≡ T₁ ; strategy-sum-coop-neut = refl
strategy-sum-coop-agg  : T₀ ⊕ T₂ ≡ T₂ ; strategy-sum-coop-agg  = refl
strategy-sum-neut-coop : T₁ ⊕ T₀ ≡ T₁ ; strategy-sum-neut-coop = refl
strategy-sum-neut-neut : T₁ ⊕ T₁ ≡ T₂ ; strategy-sum-neut-neut = refl
strategy-sum-neut-agg  : T₁ ⊕ T₂ ≡ T₀ ; strategy-sum-neut-agg  = refl
strategy-sum-agg-coop  : T₂ ⊕ T₀ ≡ T₂ ; strategy-sum-agg-coop  = refl
strategy-sum-agg-neut  : T₂ ⊕ T₁ ≡ T₀ ; strategy-sum-agg-neut  = refl
strategy-sum-agg-agg   : T₂ ⊕ T₂ ≡ T₁ ; strategy-sum-agg-agg   = refl

-- 三值策略的特征 3 性质: 同一策略叠加三次归零
-- 经济学解释: 极端策略的三重自我否定回归均衡
strategy-char3 : ∀ (s : Strategy) → (s ⊕ s) ⊕ s ≡ T₀
strategy-char3 T₀ = refl
strategy-char3 T₁ = refl
strategy-char3 T₂ = refl
