{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Examples
-- 示例与验证：律算合一基础代码运行演示 (已适配新 StateMachine 接口)

module Sovereign.Examples where

open import Data.Nat using (ℕ; _+_; _*_; _<_; _≥_; _mod_; _div_; suc; zero)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Data.Fin using (Fin; toℕ; fromℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import Sovereign.Engine.StateMachine as SM
import Sovereign.Coupling.LCM as LCM
import Sovereign.Base.Invariants as Inv
import Sovereign.Coding.Trit as T

open SM using (SovereignState; mkState; evolve)

-- 递归运行 N 步
runState : ℕ → SovereignState → SovereignState
runState zero state = state
runState (suc n) state = runState n (evolve state)

-- 1. 构造黄钟初始状态
initialState : SovereignState
initialState = mkState 
  (LCM.coordinateToSection 0)  -- section: 全 0
  Inv.POW3₁₁                   -- acc: 177147
  (Data.Fin.zero {143})        -- phase: 0 (黄钟)
  zero                         -- stepCount: 0
  zero                         -- zhonglvCount: 0
  zero                         -- singularityCount: 0
  zero                         -- localChernSum: 0

-- 2. 演化演示
stateAfter1 : SovereignState
stateAfter1 = evolve initialState

stateAfter12 : SovereignState
stateAfter12 = runState 12 initialState

-- 3. 验证
checkInitPhase : toℕ (SM.phase initialState) ≡ 0
checkInitPhase = refl

checkPhase1 : toℕ (SM.phase stateAfter1) ≡ 1
checkPhase1 = refl

-- 12 步后相位 = 12 (不是 0, 仲吕闭合只重置 acc 不重置 phase)
checkPhase12 : toℕ (SM.phase stateAfter12) ≡ 12
checkPhase12 = refl
