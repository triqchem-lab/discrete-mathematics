{-# OPTIONS --rewriting --guardedness #-}

-- | Measurement — GF(3) 离散量子测量
--
-- 连续统病态: ℂ 上的测量涉及连续谱投影 + 概率幅 |α|² ∈ ℝ
-- 离散自愈: GF(3) 上测量是有限映射, 结果 ∈ {T₀,T₁,T₂}
--
-- 核心结构:
--   §1. 离散可观测量: Qutrit → Basis3 的映射
--   §2. 投影测量: 到计算基的投影
--   §3. 测量坍缩: 态 → 基态 (构造性, 确定性, 幂等)
--   §4. 测量结果的有限性: 结果 ∈ {∣0⟩, ∣1⟩, ∣2⟩}
--   (不可克隆定理见 Quantum.NoCloning — Z[ω] 系数精确版)
--
-- 复用: Sovereign.Base.Trit, Quantum.Entanglement
-- 0 postulate.

module Sovereign.Quantum.Measurement where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Quantum.Entanglement using (
  Basis3; ∣0⟩; ∣1⟩; ∣2⟩; 0≢1; 0≢2; 1≢2;
  Qutrit; ket0; ket1; ket2)

--------------------------------------------------------------------------------
-- §1. 离散可观测量
--
-- 连续: 厄米算子 A: ℂ³ → ℂ³, 特征值 ∈ ℝ
-- 离散: 可观测量 = Qutrit → Basis3 的映射 (有限函数)
--
-- GF(3) 上只有 3 个测量结果, 无连续谱
--------------------------------------------------------------------------------

-- 可观测量: 态 → 测量结果
Observable : Set
Observable = Qutrit → Basis3

-- 计算基测量: 提取第一个非零分量的指标
-- 简化: 用第一个分量判定
computational-measure : Observable
computational-measure (T₀ , T₀ , _) = ∣2⟩
computational-measure (T₀ , _ , _) = ∣1⟩
computational-measure (_ , _ , _) = ∣0⟩

-- 基态测量结果
measure-ket0 : computational-measure ket0 ≡ ∣0⟩
measure-ket0 = refl

measure-ket1 : computational-measure ket1 ≡ ∣1⟩
measure-ket1 = refl

measure-ket2 : computational-measure ket2 ≡ ∣2⟩
measure-ket2 = refl

--------------------------------------------------------------------------------
-- §2. 投影测量
--
-- 连续: P_i = |i⟩⟨i|, 投影到第 i 个基态
-- 离散: 投影 = 判定态是否在第 i 个基态方向上
--
-- GF(3) 上投影是精确的 (无近似)
--------------------------------------------------------------------------------

-- 投影到 |0⟩: 态是 |0⟩ 的倍数吗?
projects-to-0 : Qutrit → Bool
projects-to-0 (a , T₀ , T₀) = true
projects-to-0 _ = false

--------------------------------------------------------------------------------
-- §3. 测量坍缩
--
-- 连续: 测量后态坍缩到特征态 (概率性)
-- 离散 GF(3): 基态测量是确定性的 (基态 → 对应结果)
--
-- 定理: 基态在计算基测量下不变 (已处于本征态)
--------------------------------------------------------------------------------

-- 基态是计算基测量的本征态
ket0-eigen : computational-measure ket0 ≡ ∣0⟩
ket0-eigen = refl

ket1-eigen : computational-measure ket1 ≡ ∣1⟩
ket1-eigen = refl

ket2-eigen : computational-measure ket2 ≡ ∣2⟩
ket2-eigen = refl

-- 构造性坍缩 (2026-08 P2-4): 测量后态坍缩为结果对应的基态 (确定性)
-- 连续: 概率坍缩 |ψ⟩ → Pᵢ|ψ⟩/√⟨ψ|Pᵢ|ψ⟩; 离散 GF(3): 结果即基态指标
collapse : Observable → Qutrit → Qutrit
collapse obs ψ = ketOf (obs ψ)
  where
  ketOf : Basis3 → Qutrit
  ketOf ∣0⟩ = ket0
  ketOf ∣1⟩ = ket1
  ketOf ∣2⟩ = ket2

-- 坍缩幂等: 本征态坍缩后不变 (测量本征态 = 无扰动)
collapse-eigen0 : collapse computational-measure ket0 ≡ ket0
collapse-eigen0 = refl

collapse-eigen1 : collapse computational-measure ket1 ≡ ket1
collapse-eigen1 = refl

collapse-eigen2 : collapse computational-measure ket2 ≡ ket2
collapse-eigen2 = refl

--------------------------------------------------------------------------------
-- §4. 测量结果的有限性
--
-- 连续: 测量结果可以是连续谱中的任意值
-- 离散: 测量结果 ∈ {∣0⟩, ∣1⟩, ∣2⟩}, 精确 3 个
--
-- 定理: 任何测量的结果都是三个基态之一
--------------------------------------------------------------------------------

-- 测量结果有界性
measurement-finite : ∀ (obs : Observable) (ψ : Qutrit) →
  Σ Basis3 (λ r → obs ψ ≡ r)
measurement-finite obs ψ = obs ψ , refl

-- 三个基态穷尽所有可能结果
basis-exhaustive : ∀ (r : Basis3) →
  (r ≡ ∣0⟩) ⊎ (r ≡ ∣1⟩) ⊎ (r ≡ ∣2⟩)
basis-exhaustive ∣0⟩ = inj₁ refl
basis-exhaustive ∣1⟩ = inj₂ (inj₁ refl)
basis-exhaustive ∣2⟩ = inj₂ (inj₂ refl)
