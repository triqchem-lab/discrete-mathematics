{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.GaoYangRigidLock
-- 任务书第二层·2.5：Gao-Yang 有限偏序集离散同伦的「刚性锁定」构造性核
-- （Gao, Jing-Wen; Yang, Xiao-Song, arXiv:2410.16948, 2024）
--
-- 数学背景：Gao-Yang (2024) 证明有限偏序集的离散同伦群与经典同伦群始终同构；
--   其基本现象是**有限载体上的离散环路有限步闭合**。本模块给出该现象的
--   动力学核的构造性形式化：有限类型上的**单射**端映射（可逆离散动力学 = 置换），
--   每点有限步返回原点，且返回步数有载体基数上界。
--
-- ⚠ 陈述范围（诚实边界，对照任务书 §2.5 的 rigid-lock 草案 Σ ℕ (λ n → γⁿ ≡ id)）：
--   1. 「γᵖ ≡ id」是**函数等式**——本库无 funext，一律写成**逐点**形式
--      ∀ x → orbit ρ x p ≡ x（陈述层自检①：无 funext 只能逐点，NSE.T15 同教训）。
--   2. 单射性**必要**：非单射端映射只有最终周期
--      （FiniteDynamics.orbit-eventually-periodic），「每点返回」不成立
--      （常值映射反例：p > 0 时 ρᵖ x ≢ x）。故本定理论域 = 单射端映射；
--      一般有限偏序集环路版本是 roadmap，不入本模块。
--
-- 证明路线（0 postulate）：复用 FiniteDynamics §4 轨道周期定理
--   （鸽巢碰撞 + 确定性传播），新增**单射抵消引理**把「start 前缀 + 周期」
--   剥成「纯周期」——s 次单射消去逐层剥掉 start 前缀。
--
-- 0 postulate / 0 hole。
module Sovereign.Analysis.GaoYangRigidLock where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Analysis.FiniteDynamics
  using (orbit; orbit-eventually-periodic; orbit-period-bound; EventuallyPeriodic)

--------------------------------------------------------------------------------
-- §1. 单射抵消引理：轨道相撞经 s 次单射抵消，剥掉前缀 s
--
-- 若 orbit ρ x (s + k + p) ≡ orbit ρ x (s + k)，则 orbit ρ x (k + p) ≡ orbit ρ x k。
-- 证明：对 s 归纳。suc 情形两侧类型定义归约到 orbit-step 形 ρ(orbit …)，
--   单射性直接吃掉一层 ρ。
--------------------------------------------------------------------------------

orbit-cancel-inj : {A : Set} (ρ : A → A) (x : A)
  (injρ : ∀ a b → ρ a ≡ ρ b → a ≡ b)
  (s k p : ℕ) → orbit ρ x (s + k + p) ≡ orbit ρ x (s + k)
  → orbit ρ x (k + p) ≡ orbit ρ x k
orbit-cancel-inj ρ x injρ zero k p h = h
orbit-cancel-inj ρ x injρ (suc s) k p h =
  orbit-cancel-inj ρ x injρ s k p (injρ _ _ h)

--------------------------------------------------------------------------------
-- §2. 刚性锁定（逐点形式，任务书 P2.5 构造性核）
--
-- 单射端映射 ρ : Fin n → Fin n 下，每点 x 在 period 步返回原点。
-- period 由 FiniteDynamics §4 的鸽巢机制给出。
--------------------------------------------------------------------------------

gao-yang-rigid-lock : ∀ n (ρ : Fin n → Fin n)
  (injρ : ∀ a b → ρ a ≡ ρ b → a ≡ b) (x : Fin n) →
  Σ ℕ (λ p → orbit ρ x p ≡ x)
gao-yang-rigid-lock n ρ injρ x = go (orbit-eventually-periodic n ρ x)
  where
    go : EventuallyPeriodic (λ m → orbit ρ x m) → Σ ℕ (λ p → orbit ρ x p ≡ x)
    go ep =
      EventuallyPeriodic.period ep ,
      orbit-cancel-inj ρ x injρ (EventuallyPeriodic.start ep) 0
        (EventuallyPeriodic.period ep) (EventuallyPeriodic.periodic ep zero)
    -- periodic zero : orbit (start + 0 + period) ≡ orbit (start + 0)
    -- 抵消后        : orbit (0 + period) ≡ orbit (0 + 0)，定义归约即 orbit period ≡ x

-- 返回步数有载体基数上界（period ≤ 载体大小）
gao-yang-rigid-lock-bound : ∀ N (ρ : Fin (suc N) → Fin (suc N))
  (injρ : ∀ a b → ρ a ≡ ρ b → a ≡ b) (x : Fin (suc N)) →
  Σ ℕ (λ p → (orbit ρ x p ≡ x) × (p ≤ suc N))
gao-yang-rigid-lock-bound N ρ injρ x =
  let (p , p≤sN , s , h) = orbit-period-bound N ρ x
  in  p , (orbit-cancel-inj ρ x injρ s 0 p (h zero) , p≤sN)

--------------------------------------------------------------------------------
-- §3. 具体点对抗（对抗验证协议 §6）：Fin 3 轮换 [1,2,0]
--
-- 三步逐点归零（3 case refl，独立于定理）+ 单射性（9 case refl）。
-- 与定理实例互证：rot3 是 gao-yang-rigid-lock 3 rot3 rot3-inj 的合法输入。
--------------------------------------------------------------------------------

rot3 : Fin 3 → Fin 3
rot3 fzero = fsuc fzero
rot3 (fsuc fzero) = fsuc (fsuc fzero)
rot3 (fsuc (fsuc fzero)) = fzero

rot3-inj : ∀ a b → rot3 a ≡ rot3 b → a ≡ b
rot3-inj fzero fzero eq = refl
rot3-inj fzero (fsuc fzero) ()
rot3-inj fzero (fsuc (fsuc fzero)) ()
rot3-inj (fsuc fzero) fzero ()
rot3-inj (fsuc fzero) (fsuc fzero) eq = refl
rot3-inj (fsuc fzero) (fsuc (fsuc fzero)) ()
rot3-inj (fsuc (fsuc fzero)) fzero ()
rot3-inj (fsuc (fsuc fzero)) (fsuc fzero) ()
rot3-inj (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) eq = refl

rot3-lock : ∀ (x : Fin 3) → orbit rot3 x 3 ≡ x
rot3-lock fzero = refl
rot3-lock (fsuc fzero) = refl
rot3-lock (fsuc (fsuc fzero)) = refl

-- 定理实例与具体点互证：rot3 的返回步数 p 还满足 p ≤ 3
rot3-lock-bound : Σ ℕ (λ p → (orbit rot3 fzero p ≡ fzero) × (p ≤ 3))
rot3-lock-bound = gao-yang-rigid-lock-bound 2 rot3 rot3-inj fzero
