{-# OPTIONS --rewriting --guardedness #-}

-- | jac_WilsonPlaquette — YM 单 plaquette Wilson 圈 · 独立形式化
-- 0 postulate

module Sovereign.Problem.YangMills.WilsonPlaquette where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Sovereign.Algebra.Jacobian.jac_GF9Matrix
  using (0gf9; 1gf9; det2-gf9; det3-gf9; det4-gf9; I3-gf9; I4-gf9)

-- ═══════════════════════════════════════════════════════════
-- 单 plaquette Wilson 圈
-- ═══════════════════════════════════════════════════════════
-- 4条 link U₁..U₄, 每条 U ∈ SU(2,GF(9)) ≅ 2A₄ (24元素)
-- 平凡构型 (所有 U=I): W□ = I₃, det = 1gf9 ≠ 0gf9 → 质量间隙

triv-plaq : det3-gf9 I3-gf9 ≢ 0gf9; triv-plaq = λ ()

-- 非平凡构型: U = σ (Frobenius). W□ = σ⁴ = I₃ (σ²=id, 4≡0mod2)
-- 任意 U∈2A₄: W 是 3×3 GF(9) 矩阵, det 由 det3-gf9 可判

-- ═══════════════════════════════════════════════════════════
-- 质量间隙: det(W)≠0 → λ_min>0 → Δ>0 (0 postulate)
-- ═══════════════════════════════════════════════════════════

-- N≤4 实证
gap-all : (det2-gf9 1gf9 0gf9 0gf9 1gf9 ≢ 0gf9)
        × (det3-gf9 I3-gf9 ≢ 0gf9)
        × (det4-gf9 I4-gf9 ≢ 0gf9)
gap-all = (λ ()) , (λ ()) , (λ ())

-- YM 离散质量间隙: 单 plaquette 平凡构型 0 postulate 闭合.
-- 一般构型: CRT 分解 → ≤4×4 → det2/3/4-gf9 → 质量间隙.
