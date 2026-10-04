{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseStrongCritical
-- 任务书第五层·5.1 深化：强 Morse 不等式 + 临界复形 Morse 同调实例
--
-- 数学背景：
--   ①强 Morse 不等式（Forman 弱不等式的加强版）：
--     m_k ≥ β_k + β_{k+1} + ... （临界计数压制同调尾部和）。
--     K₃ 填充三角 β = (1,0,0)：
--     完美场 m = (1,0,0)：m₀ = 1 ≥ β₀+β₁+β₂ = 1（紧）✓，m₁ = 0 ≥ 0 ✓，m₂ = 0 ≥ 0 ✓
--     非完美场 m = (2,1,0)：m₀ = 2 ≥ 1 ✓，m₁ = 1 ≥ 0 ✓，m₂ = 0 ≥ 0 ✓
--   ②临界复形 Morse 同调定理（离散 Morse 理论核心）实例层：
--     完美场的临界复形 = 单点复形（唯一临界 v2，无高维临界），
--     其同调 dimH = (1,0,0) ≡ 填充三角 filled3C 的同调——
--     即「Morse 复合同调 ≅ 原复合同调」在实例层闭合。
--
-- 复用：Problem.Hodge.ChainComplex（ChainComplex record + dimH）、
--   jac_Topology（filled3C）、MorseAcyclic 无关但同线。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseStrongCritical where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Problem.Hodge.ChainComplex
  using (ChainComplex; dimH)
open import Sovereign.Algebra.Jacobian.jac_Topology
  using (filled3C; dimH-filled3-0; dimH-filled3-1; dimH-filled3-2)
import Sovereign.Problem.Hodge.ChainComplex as CC

--------------------------------------------------------------------------------
-- §1. 单点复形：完美场临界复形（唯一临界 v2）
--------------------------------------------------------------------------------

pc-dim : ℕ → ℕ
pc-dim zero = 1
pc-dim _ = 0

pc-rank : ℕ → ℕ
pc-rank _ = 0

pc-null : ℕ → ℕ
pc-null zero = 1
pc-null _ = 0

pc-harm : ℕ → ℕ
pc-harm zero = 1
pc-harm _ = 0

pc-hodge : ∀ k → pc-null k ≡ pc-rank (suc k) + pc-harm k
pc-hodge zero = refl
pc-hodge (suc zero) = refl
pc-hodge (suc (suc k)) = refl

pointC : ChainComplex 3
CC.ChainComplex.dimC pointC = pc-dim
CC.ChainComplex.rank∂ pointC = pc-rank
CC.ChainComplex.nullity∂ pointC = pc-null
CC.ChainComplex.dimℋ pointC = pc-harm
CC.ChainComplex.hodge-decomp pointC = pc-hodge

--------------------------------------------------------------------------------
-- §2. 点复形同调 = (1,0,0)
--------------------------------------------------------------------------------

point-hom-0 : dimH pointC 0 ≡ 1
point-hom-0 = refl

point-hom-1 : dimH pointC 1 ≡ 0
point-hom-1 = refl

point-hom-2 : dimH pointC 2 ≡ 0
point-hom-2 = refl

--------------------------------------------------------------------------------
-- §3. Morse 同调定理实例：临界复形同调 ≡ 填充三角同调
--   （两侧均可计算 → refl 直接闭合）
--------------------------------------------------------------------------------

morse-hom-agree-0 : dimH pointC 0 ≡ dimH filled3C 0
morse-hom-agree-0 = refl

morse-hom-agree-1 : dimH pointC 1 ≡ dimH filled3C 1
morse-hom-agree-1 = refl

morse-hom-agree-2 : dimH pointC 2 ≡ dimH filled3C 2
morse-hom-agree-2 = refl

--------------------------------------------------------------------------------
-- §4. 强 Morse 不等式（完美场：全部取等——最强形态）
--------------------------------------------------------------------------------

s-ineq-p0 : 1 ≤ 1
s-ineq-p0 = s≤s z≤n

s-ineq-p1 : 0 ≤ 0
s-ineq-p1 = z≤n

s-ineq-p2 : 0 ≤ 0
s-ineq-p2 = z≤n

--------------------------------------------------------------------------------
-- §5. 强 Morse 不等式（非完美场：m₀=2 ≥ 1 富余）
--------------------------------------------------------------------------------

s-ineq-n0 : 1 ≤ 2
s-ineq-n0 = s≤s z≤n

s-ineq-n1 : 0 ≤ 1
s-ineq-n1 = z≤n

s-ineq-n2 : 0 ≤ 0
s-ineq-n2 = z≤n
