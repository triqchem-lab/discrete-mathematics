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

-- CRT 理论
open import Sovereign.Format.CRT public
