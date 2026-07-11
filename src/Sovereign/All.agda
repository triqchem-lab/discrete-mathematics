{-# OPTIONS --cubical --guardedness #-}

module Sovereign.All where

open import Sovereign.Base.Trit          public using (Trit; T-; T0; T+)
open import Sovereign.Base.Invariants    public using (POLAR_WINDING; TOROIDAL_WINDING; CHERN_NUMBER; SOVEREIGN_LCM)
open import Sovereign.Base.Axioms        public using (digitalRoot; IsStable; zhonglvAlign)
open import Sovereign.Structology.Lattice public using (Lü; TwelveLu)
open import Sovereign.Structology.Closure public using (State; step; isZhonglvPoint)
open import Sovereign.Topology.HighDimClosure public using (HighDimView; EngineeringView)
open import Sovereign.MetaStructure.WuXing public using (WuXing; generate; overcome)
open import Sovereign.Format.TQ10        public using (TQ10Block; isBlockValid)
open import Sovereign.Coupling.Dynamics  public using (evolveN) renaming (step to dynStep)
open import Sovereign.Engine.StateMachine public using (SovereignState; evolve)

-- 量子数学公理基础
open import Sovereign.Quantum.Foundation public
  using (superposition-table-verified; lcm-modulus; spiral-trit-1;
         spiral-trit-2; spiral-trit-4; spiral-trit-7; spiral-trit-8)

-- CRT 理论
open import Sovereign.Format.CRT public

-- 定理17: 玄武吸水 (自我修复) — StepNotEq 一阶谓词化隔离 OOM
open import Sovereign.Structology.XuanwuAbsorption public
  using (theorem-17-xuanwu; never-stops; xuanwu-selfheal;
         full-tour-identity; bezout-13-46)

-- 量子数学桥: CRT↔幻方↔T⁶环面↔五行
open import Sovereign.Structology.QuantumBridge public
  using (wuXing-sum-25; magic-34-minus-wuxing-25; full-tour-6624;
         polar-is-A4-squared; m-mod-fulltour; tours-per-M)

-- M4 幻方正交拓扑
open import Sovereign.Structology.MagicSquareM4 public
  using (M4; magicConstant; crtCongruence; Orth; orth-16-neg16;
         eigenvector34; eigenvector0; eigenEq34; eigenEq0)
