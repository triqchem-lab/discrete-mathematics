{-# OPTIONS --rewriting --guardedness #-}
module CkIter where
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GroupTheory.DuodecClockProperties
  -- 不行, 它也依赖坏文件
