{-# OPTIONS --guardedness #-}
module ProbeH where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Integer.Base using (ℤ; _+_; 0ℤ)
open import Data.Integer.Tactic.RingSolver using (solve-∀)

-- 目标：6 项加法转置恒等式（sum3-comm 核心形）
test : ∀ a b c d e f →
  (a + (b + c)) + ((d + (e + f)) + 0ℤ) ≡
  ((a + (d + 0ℤ)) + ((b + (e + 0ℤ)) + (c + (f + 0ℤ))))
test = solve-∀
