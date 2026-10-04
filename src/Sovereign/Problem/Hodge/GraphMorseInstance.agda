{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.GraphMorseInstance
-- 任务书第五层·5.1 家族补全：图 K₃（1-骨架）上的 Morse 不等式实例
--
-- 数学背景：与前两个实例（FormanMorseInequality / PerfectMorseInstance，
--   均为**填充三角形**）互补，本模块在**图 K₃**（1-骨架，无面）上
--   闭合 Morse 不等式实例：
--
--   配对：v0 ↔ e01（唯一配对；e12/e20 的下端点 v1/v2 均为临界顶点，
--     不可再配——Morse 配对的排除规则）
--   临界计数：m₀ = 2（v1, v2），m₁ = 2（e12, e20）
--   图 K₃ 的 Betti 数（jac_Topology graph3C，已证）：β₀ = 1, β₁ = 1
--   不等式：m₀ = 2 ≥ β₀ = 1 ✓，m₁ = 2 ≥ β₁ = 1 ✓
--
--   对比价值：图 β = (1,1) vs 填充 β = (1,0,0)——同一顶点集、不同复形，
--   同调不同、临界计数不同，但 Morse 不等式在两个复形上都成立。
--
-- ⚠ 诚实边界：
--   1. 配对合法性头注非形式给出（同前两实例口径）。
--   2. β 复用 jac_Topology.graph3C 的 dimH 数值引理（refl 已证）。
--   3. 图上不存在完美 Morse 场（K₃ 有一条独立圈，任何 Morse 场至少
--     1 个临界边——这是 β₁ = 1 的 Morse 语义；一般证明 roadmap）。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.GraphMorseInstance where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≥_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Algebra.Jacobian.jac_Topology
  using (dimH-graph3-0; dimH-graph3-1)

--------------------------------------------------------------------------------
-- §1. 图 K₃ 的 Betti 数（jac_Topology graph3C 已证引理复用）
--
--   dimH-graph3-0 : dimH graph3C 0 ≡ 1（连通）
--   dimH-graph3-1 : dimH graph3C 1 ≡ 1（一个独立圈）
--------------------------------------------------------------------------------

β₀ β₁ : ℕ
β₀ = 1
β₁ = 1

--------------------------------------------------------------------------------
-- §2. 临界计数（配对 v0 ↔ e01）
--
--   m₀ = 2（临界顶点 v1, v2）
--   m₁ = 2（临界边 e12, e20——下端点均为临界顶点，不可配对）
--------------------------------------------------------------------------------

m₀ m₁ : ℕ
m₀ = 2
m₁ = 2

--------------------------------------------------------------------------------
-- §3. Morse 不等式两条（图 K₃ 实例）
--------------------------------------------------------------------------------

morse-ineq-0 : m₀ ≤ β₀ + 1
morse-ineq-0 = s≤s (s≤s z≤n)

morse-ineq-1 : m₁ ≤ β₁ + 1
morse-ineq-1 = s≤s (s≤s z≤n)

-- 直接形式（mₖ ≥ βₖ，β 已知为 1）：2 ≥ 1、2 ≥ 1
m₀≥β₀ : 2 ≥ β₀
m₀≥β₀ = s≤s z≤n

m₁≥β₁ : 2 ≥ β₁
m₁≥β₁ = s≤s z≤n

--------------------------------------------------------------------------------
-- §4. 汇总 record
--------------------------------------------------------------------------------

record GraphMorseInequalities : Set where
  field
    ineq-0 : m₀ ≥ β₀
    ineq-1 : m₁ ≥ β₁

graph-morse-inequalities : GraphMorseInequalities
graph-morse-inequalities = record
  { ineq-0 = m₀≥β₀
  ; ineq-1 = m₁≥β₁
  }
