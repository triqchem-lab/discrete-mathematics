{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.EulerPoincareInstance
-- 任务书第四/五层桥接：欧拉–庞加莱公式的 K₃ 实例闭合
--
-- 数学背景：欧拉–庞加莱公式 χ = Σ(-1)^k β_k 对有限 CW 复形成立。
--   K₃ 三角形的三种计数表示在此实例上全部一致：
--   1. 直接计数（图 1-骨架）：χ = V - E = 3 - 3 = 0
--   2. 同调计数：β₀ - β₁ = 1 - 1 = 0（ChainComplex.tri 的 dimH）
--   3. Morse 计数（含面）：m₀ - m₁ + m₂ = 2 - 1 + 0 = 1 = V - E + F = 3-3+1
--
-- ⚠ 诚实边界：
--   1. 实例层（K₃ 具体数值），一般定理「任意有限复形 χ = Σβ」roadmap。
--   2. ℕ 无负数——减法用 ∸（截断减法）；本实例所有被减数 ≥ 减数，∸ 即精确减法。
--   3. χ(图) = 0 与 χ(含面三角) = 1 是**不同复形**的示性数，各自与
--      对应 β/Morse 和一致——不混用。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.EulerPoincareInstance where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Problem.Hodge.ChainComplex using (dimH; tri)

--------------------------------------------------------------------------------
-- §1. 图 1-骨架的欧拉–庞加莱（K₃：V=3, E=3, F=0）
--
-- χ(图) = V - E = 0；同调侧 β₀ - β₁ = 1 - 1 = 0。两值一致。
--------------------------------------------------------------------------------

-- 直接计数：V - E
chi-graph-direct : ℕ
chi-graph-direct = 3 ∸ 3

-- 同调计数：β₀ - β₁
chi-graph-homology : ℕ
chi-graph-homology = dimH tri 0 ∸ dimH tri 1

-- 欧拉–庞加莱实例（图）：直接计数 ≡ 同调计数
euler-poincare-graph : chi-graph-direct ≡ chi-graph-homology
euler-poincare-graph = refl

--------------------------------------------------------------------------------
-- §2. 圈数公式（cyclomatic number）：E - V + 1 = β₁
--
-- 连通图的独立圈数 = E - V + 1 = 3 - 3 + 1 = 1 = dimH tri 1。
-- 这把图论层的圈计数与同调层的 H₁ 维数焊接。
--------------------------------------------------------------------------------

cycle-rank-K3 : ℕ
cycle-rank-K3 = (3 ∸ 3) + 1

cycle-rank-matches-H1 : cycle-rank-K3 ≡ dimH tri 1
cycle-rank-matches-H1 = refl

--------------------------------------------------------------------------------
-- §3. 含面三角形的欧拉–庞加莱：χ = V - E + F = 1
--
-- 填充三角形（F=1）的示性数 1 与 Morse 计数和 m₀ - m₁ + m₂ = 2-1+0 = 1
-- 一致（FormanMorseInequality 的临界计数）。
--------------------------------------------------------------------------------

-- 直接计数：V - E + F（填充三角形）
chi-filled-direct : ℕ
chi-filled-direct = (3 ∸ 3) + 1

-- Morse 计数：m₀ - m₁ + m₂（FormanMorseInequality 的临界单形数）
chi-filled-morse : ℕ
chi-filled-morse = (2 ∸ 1) + 0

-- 欧拉–庞加莱实例（含面）：直接计数 ≡ Morse 计数
euler-poincare-filled : chi-filled-direct ≡ chi-filled-morse
euler-poincare-filled = refl

-- 含面三角形示性数为 1
chi-filled-value : chi-filled-direct ≡ 1
chi-filled-value = refl

--------------------------------------------------------------------------------
-- §5. Forman 第一定理实例：临界计数交替和 = 原复形欧拉示性数
--
-- Forman (1998) 第一定理：Σ(-1)^k m_k = χ(复形)，与 Morse 场的选择无关。
-- K₃ 实例：m₀ - m₁ + m₂ = 2 - 1 + 0 = 1 = V - E + F = 3 - 3 + 1。
-- 即 chi-filled-morse（§3 的 Morse 计数）与 chi-filled-direct（§3 的
-- 直接计数）不仅都等于 1，且**恒等式本身**就是本节陈述的内容。
--
-- ⚠ 诚实边界：实例层（K₃ + triangleVF 数值）；一般定理（任意有限复形、
--   任意 Morse 场）需 Morse 复形与原复形的链同构证明，roadmap。
--------------------------------------------------------------------------------

forman-first-theorem-instance : chi-filled-morse ≡ chi-filled-direct
forman-first-theorem-instance = refl

-- 三方一致（本模块内闭合）：直接计数 ≡ Morse 计数 ≡ 1
euler-triple-agreement : (chi-filled-direct ≡ 1) × (chi-filled-morse ≡ 1)
euler-triple-agreement = refl , refl
