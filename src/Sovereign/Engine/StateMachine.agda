{-# OPTIONS --guardedness #-}
module Sovereign.Engine.StateMachine where
open import Data.Nat using (ℕ; suc; _+_; _*_; _<_; _≤_)
open import Data.Nat.Base using (_≡ᵇ_; _%_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Vec using (Vec; map; []; _∷_; replicate)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Sovereign.Coupling.LCM as LCM
import Sovereign.Coding.Trit as T
import Sovereign.Base.Axioms as Ax
import Sovereign.Base.Invariants as Inv

record SovereignState : Set where
  constructor mkState
  field
    section : LCM.SovereignSection ; acc : ℕ ; phase : Fin 144
    stepCount : ℕ ; zhonglvCount : ℕ ; singularityCount : ℕ ; localChernSum : ℕ
open SovereignState public

stepPhase : Fin 144 → Fin 144 ; stepPhase p = (toℕ p + 1) mod 144

stepSection : LCM.SovereignSection → Fin 144 → LCM.SovereignSection
stepSection sec phase =
  let isEven = toℕ (toℕ phase mod 2) ≡ᵇ 0
      delta  = if isEven then suc (suc zero) else suc zero
  in map (λ t → t T.⊕ delta) sec

evolve : SovereignState → SovereignState
evolve state =
  let sec = section state ; ph = phase state ; nextPh = stepPhase ph
      nextSec = stepSection sec ph ; steps = stepCount state
      av = SovereignState.acc state
      isZh = toℕ (toℕ ph mod 12) ≡ᵇ 11
      newAcc = if isZh then Ax.zhonglvAlign av else (av + Inv.SOVEREIGN_LCM) % Inv.SOVEREIGN_LCM
      newZhCt = if isZh then zhonglvCount state + 1 else zhonglvCount state
  in mkState nextSec newAcc nextPh (suc steps) newZhCt (singularityCount state) (localChernSum state)

stateToTQ10 : SovereignState → Vec ℕ 6 ; stateToTQ10 state = LCM.packSectionToQs (section state)
tq10ToState : Vec ℕ 6 → SovereignState ; tq10ToState qs = mkState (LCM.unpackQsToSection qs) 0 zero 0 0 0 0

-- 仲吕触发阈值：每 12 步检查一次（phase mod 12 ≡ 11）
zhonglvTriggeredAfter12 : ℕ → Set
zhonglvTriggeredAfter12 steps = 12 ≤ steps

-- 能隙奇点计数：无效输入导致奇点累积
gapSingularityIncreasesOnInvalidInput : ℕ → ℕ → Set
gapSingularityIncreasesOnInvalidInput before after = before < after

-- LCM 保持性质：检查 evolve 后的 section 坐标是否在 LCM 范围内
evolvePreservesLCM : SovereignState → Set
evolvePreservesLCM state = LCM.sectionToCoordinate (section (evolve state)) < Inv.SOVEREIGN_LCM
