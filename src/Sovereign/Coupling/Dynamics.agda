{-# OPTIONS --allow-unsolved-metas #-}

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
