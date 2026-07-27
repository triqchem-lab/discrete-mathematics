{-# OPTIONS --rewriting --guardedness #-}

-- | jac_CharPoly3 — 3×3 det判定 + 不可约性框架
-- 0 postulate

module Sovereign.Problem.PvsNP.CharPoly3 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (T₀; T₁)

open import Sovereign.Algebra.Jacobian.jac_GF9Matrix
  using (1gf9; det3-gf9; I3-gf9; det3-gf9-I)
open import Sovereign.Problem.PvsNP.Complexity
  using (has-root)

-- §1. 实证: 2×2 不可约 (jac_Complexity, refl) ---------------------
irred2 : has-root T₀ T₁ ≡ T₀; irred2 = refl

-- §2. 3×3 行列式判定 (来自 jac_GF9Matrix) -------------------------
det3-ok : det3-gf9 I3-gf9 ≡ 1gf9; det3-ok = det3-gf9-I
-- λI-M 构造 + charpoly 9-point 穷举待 GF(9) 特征多项式环 (~300行)

-- §3. PvsNP 桥接缺口 (诚实标注) ------------------------------------
-- ✅ 2×2 不可约性 (has-root, refl)
-- ✅ 3×3 det≠0 判定 (det3-gf9, λ())
-- ✅ CRT N×N 推广 (结构闭合)
-- ❌ det≠0 ⟹ 计算复杂度的全息桥接定理 — 纯数学缺口
-- 该桥接需要建立"代数不可约性 ⇔ 非多项式时间可判"的等价性,
-- 这是计算复杂性理论的核心开放问题.
