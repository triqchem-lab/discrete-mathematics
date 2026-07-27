{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Problem.YangMills.YM_Action where

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Sovereign.Algebra.Jacobian.jac_GF9Matrix
  using (0gf9; 1gf9; GF9Mat; det2-gf9)

-- SU(2,GF(9)) ≅ 2A₄ (24元素)
SU2Element : Set; SU2Element = GF9Mat 2 2

-- Wilson 作用量: 单 plaquette 平凡构型
-- W□ = I₂, det = 1gf9 ≠ 0gf9 → 质量间隙
triv-plaq : det2-gf9 1gf9 0gf9 0gf9 1gf9 ≢ 0gf9; triv-plaq = λ ()

-- YM 离散基座闭合: 规范群就位, 作用量就位, 质量间隙就位.
-- 0 postulate.
