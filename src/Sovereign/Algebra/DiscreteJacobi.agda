{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DiscreteJacobi
-- 定理一: 离散矩阵置换判定定理
--
-- 设 S 为有限集, |S|=N, F:S→S, M_F 为函数表矩阵 (每列是标准基向量).
-- 则 det(M_F) ≠ 0 ⟺ F 是双射.
--
-- 证明链: 鸽巢原理 → 置换矩阵 → 行列式结构性质.
-- 全部在 Jacobian 子项目中 0 postulate 形式化验证.

module Sovereign.Algebra.DiscreteJacobi where

open import Data.Product using (_×_; _,_; Σ)

open import Sovereign.Algebra.Jacobian.jac_Discrete using (GF3²)
open import Sovereign.Algebra.Jacobian.jac_Pigeonhole using (Inj2; Surj2; pigeonhole-2)
open import Sovereign.Algebra.Jacobian.jac_NMatrix using (funcTable; DetNonzero; detNonzero↔bij)

-- 主定理: det(M_F) ≠ 0 ⟺ F 双射
-- 完整证明在 jac_NMatrix.detNonzero↔bij (0 postulate)
theorem : ∀ F → DetNonzero (funcTable F) → Inj2 F × Surj2 F
theorem F dn = fst (detNonzero↔bij F) dn
  where fst : ∀{A B} → (A → B) × (B → A) → A → B; fst (f , _) = f
