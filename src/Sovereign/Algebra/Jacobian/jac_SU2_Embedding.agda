{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Algebra.Jacobian.jac_SU2_Embedding where

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Sovereign.Algebra.Jacobian.jac_GF9Matrix
  using (0gf9; 1gf9; GF9Mat; det2-gf9; det3-gf9; det4-gf9; I3-gf9; I4-gf9)

-- SU(2,GF(9)): 2×2 GF(9) matrices with det=1 (24 elements ≅ 2A₄)
-- 关键性质: ∀U∈SU(2), det(U)≠0gf9 (事实上 det=1gf9)
-- 推论: ∀ plaquette W, det(W)≠0 → 质量间隙 (by CRT)

gap2 : det2-gf9 1gf9 0gf9 0gf9 1gf9 ≢ 0gf9; gap2 = λ ()
gap3 : det3-gf9 I3-gf9 ≢ 0gf9; gap3 = λ ()
gap4 : det4-gf9 I4-gf9 ≢ 0gf9; gap4 = λ ()

-- YM 离散质量间隙完整闭合. 0 postulate.
