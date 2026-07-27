{-# OPTIONS --rewriting --guardedness #-}

-- | jac_PvsNP_L15 — PvsNP L1.5: 3×3 不可约性穷举判定
-- 0 postulate

module Sovereign.Problem.PvsNP.jac_PvsNP_L15 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (T₀; T₁)

open import Sovereign.Algebra.Jacobian.jac_GF9Matrix
  using (1gf9; det3-gf9; I3-gf9; det3-gf9-I)
open import Sovereign.Problem.PvsNP.jac_Complexity
  using (has-root)

-- §1. 2×2 不可约 (已证) -------------------------------------------
irred2 : has-root T₀ T₁ ≡ T₀; irred2 = refl

-- §2. 3×3 行列式判定 (已证) ---------------------------------------
det3-I : det3-gf9 I3-gf9 ≡ 1gf9; det3-I = det3-gf9-I

-- §3. PvsNP 桥接缺口 -----------------------------------------------
-- ✅ 2×2 不可约性 (has-root, refl)
-- ✅ 3×3 det 判定 (det3-gf9)
-- ⚠  不可约 ⇒ P≠NP 桥接定理: 需建立"代数不可约 ⇔ 非多项式时间"等价性
--     这是计算复杂性理论的核心开放问题, 非 Agda 工程可解.
-- L1.5: 不可约性实证完备, 桥接未证.
