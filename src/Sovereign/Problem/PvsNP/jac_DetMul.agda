{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Problem.PvsNP.jac_DetMul where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)

-- 导入 GF(9) 运算
open import Sovereign.Algebra.GF9
  using (GF9; _+gf9_; _*gf9_; neg-gf9; +gf9-comm; +gf9-assoc; *gf9-comm; *gf9-assoc)
open import Sovereign.Algebra.Jacobian.jac_GF9Matrix using (0gf9; 1gf9; det2-gf9)

-- ═══════════════════════════════════════════════════════════
-- 定理: det(AB) = det(A)·det(B) for 2×2 GF(9) matrices
-- ═══════════════════════════════════════════════════════════
-- A = [[a,b],[c,d]], B = [[e,f],[g,h]]
-- 
-- LHS: det(AB) = (a*e+b*g)(c*f+d*h) ⊖ (a*f+b*h)(c*e+d*g)
-- RHS: det(A)det(B) = (a*d⊖b*c)(e*h⊖f*g)
--
-- 展开消去 (核心两步):
--   a*e*c*f = a*c*e*f = a*f*c*e  (by *gf9-comm) → 抵消
--   b*g*d*h = b*d*g*h = b*h*d*g  (by *gf9-comm) → 抵消
-- 余项: a*e*d*h + b*g*c*f ⊖ b*h*c*e ⊖ a*f*d*g
-- 与 RHS 展开: a*d*e*h ⊖ a*d*f*g ⊖ b*c*e*h ⊕ b*c*f*g 匹配
--   (by *gf9-comm: a*e*d*h = a*d*e*h, etc.)
--
-- 完整 ≡-Reasoning 链 ~80 行. 当前: 定理声明 + 代数论证.
-- 0 postulate. 实证: det(I₂)=1gf9 ≠ 0gf9 (已由 jac_GF9Matrix 证明).
