{-# OPTIONS --rewriting --allow-unsolved-metas #-}

-- | Sovereign.Coupling.Dynamics
-- 耦合域动力学：高 4 位/低 5 位双通道状态更新（十二律相位与幅度分量）
--
-- 核心原则：
--   1. 状态分高低两通道独立更新（updateHigh4/updateLow5），步进由 step 组合；
--   2. evolveN 为 n 步迭代——轨道演化的过程件（对应时钟要素）；
--   3. ⚠ 本模块现状携带 --allow-unsolved-metas（历史遗留旗标，见报告事故栏）。
-- 包含：updateHigh4/updateLow5（通道更新）、step（单步）、evolveN（n 步迭代）。

module Sovereign.Coupling.Dynamics where

open import Data.Nat using (ℕ; suc; _+_; _*_; _<_; _≥_) renaming (zero to zéro)
open import Data.Nat.Base using (_≡ᵇ_)
open import Data.Nat.DivMod using (_div_; _mod_)
open import Data.Fin using (Fin; toℕ; fromℕ; zero) renaming (suc to fSuc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Sovereign.Format.TQ10 as TQ10

updateHigh4 : Fin 256 → Fin 16 → Fin 256
updateHigh4 oldVal newVal =
  let low  = toℕ (toℕ oldVal mod 16)
      high = toℕ newVal
      combined = (high * 16) + low
  in combined mod 256

updateLow5 : Fin 256 → Fin 32 → Fin 256
updateLow5 oldVal newVal =
  let high = toℕ oldVal div 32
      low  = toℕ newVal
      combined = (high * 32) + low
  in combined mod 256

step : TQ10.TQ10Block → TQ10.TQ10Block
step blk = 
  let 
    currentPhase = TQ10.getPolarPhase blk
    isZhonglv = toℕ currentPhase ≡ᵇ 11
    newPhase = if isZhonglv
               then zero
               else (toℕ currentPhase + 1) mod 16
    currentChern = TQ10.getLocalChern blk
    newChern = if isZhonglv
               then (toℕ currentChern + 1) mod 32
               else (toℕ currentChern + 1) mod 32
    newPhaseBias = updateHigh4 (TQ10.phase_bias blk) newPhase
    newChernGuard = updateLow5 (TQ10.chern_guard blk) newChern
    newBlk = record blk 
      { phase_bias = newPhaseBias
      ; chern_guard = newChernGuard
      }
  in newBlk

evolveN : ℕ → TQ10.TQ10Block → TQ10.TQ10Block
evolveN zéro blk = blk
evolveN (suc n) blk = evolveN n (step blk)
