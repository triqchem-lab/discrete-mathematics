{-# OPTIONS --rewriting #-}
module Generated.T6Verification where

open import Data.Nat using (_≤_)
open import Sovereign.Structology.T6
-- Da-Yan Engine auto-generated
postulate
  all-729-bounded : (x : T6Lattice) → toℕ-sum x ≤ 728
