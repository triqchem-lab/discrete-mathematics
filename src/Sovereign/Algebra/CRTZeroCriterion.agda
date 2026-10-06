{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.CRTZeroCriterion
-- P0-2 零点判据：crt12 x y ≡ d0 ⟺ x ≡ T₀ ∧ y ≡ zero
--
-- 12 case 枚举：crt12 表中只有 (T₀, zero) 映到 d0。
-- 由 crt12-roundtrip：det M = d0 ⟺ π3(det M) = T₀ ∧ π4(det M) = zero。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.CRTZeroCriterion where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Duodecimal using (Duodec; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11; crt12)

-- Duodec 不等式（构造子不相等——λ () 空模式匹配）
d0≢d1 : d0 ≡ d1 → ⊥; d0≢d1 ()
d0≢d2 : d0 ≡ d2 → ⊥; d0≢d2 ()
d0≢d3 : d0 ≡ d3 → ⊥; d0≢d3 ()
d0≢d4 : d0 ≡ d4 → ⊥; d0≢d4 ()
d0≢d5 : d0 ≡ d5 → ⊥; d0≢d5 ()
d0≢d6 : d0 ≡ d6 → ⊥; d0≢d6 ()
d0≢d7 : d0 ≡ d7 → ⊥; d0≢d7 ()
d0≢d8 : d0 ≡ d8 → ⊥; d0≢d8 ()
d0≢d9 : d0 ≡ d9 → ⊥; d0≢d9 ()
d0≢d10 : d0 ≡ d10 → ⊥; d0≢d10 ()
d0≢d11 : d0 ≡ d11 → ⊥; d0≢d11 ()

-- CRT 零点判据：crt12 x y ≡ d0 ⟺ x ≡ T₀ ∧ y ≡ zero
-- 正向：12 case 枚举，只有 (T₀, zero) 满足
crt12-zero-fwd : ∀ (x : Trit) (y : Fin 4) → crt12 x y ≡ d0 → x ≡ T₀ × y ≡ fzero
crt12-zero-fwd T₀ fzero eq = (refl , refl)
crt12-zero-fwd T₀ (fsuc fzero) eq = ⊥-elim (d0≢d9 (sym eq))
crt12-zero-fwd T₀ (fsuc (fsuc fzero)) eq = ⊥-elim (d0≢d6 (sym eq))
crt12-zero-fwd T₀ (fsuc (fsuc (fsuc fzero))) eq = ⊥-elim (d0≢d3 (sym eq))
crt12-zero-fwd T₁ fzero eq = ⊥-elim (d0≢d4 (sym eq))
crt12-zero-fwd T₁ (fsuc fzero) eq = ⊥-elim (d0≢d1 (sym eq))
crt12-zero-fwd T₁ (fsuc (fsuc fzero)) eq = ⊥-elim (d0≢d10 (sym eq))
crt12-zero-fwd T₁ (fsuc (fsuc (fsuc fzero))) eq = ⊥-elim (d0≢d7 (sym eq))
crt12-zero-fwd T₂ fzero eq = ⊥-elim (d0≢d8 (sym eq))
crt12-zero-fwd T₂ (fsuc fzero) eq = ⊥-elim (d0≢d5 (sym eq))
crt12-zero-fwd T₂ (fsuc (fsuc fzero)) eq = ⊥-elim (d0≢d2 (sym eq))
crt12-zero-fwd T₂ (fsuc (fsuc (fsuc fzero))) eq = ⊥-elim (d0≢d11 (sym eq))

-- 反向：refl
crt12-zero-rev : crt12 T₀ fzero ≡ d0
crt12-zero-rev = refl

-- 组合：det M = d0 ⟺ π3(det M) = T₀ ∧ π4(det M) = zero
-- 由 crt12-roundtrip + crt12-zero-fwd/rev
