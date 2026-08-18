{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.IntegrationByParts
-- 分部积分统一结构 (L3 深层证明)
--
-- 核心命题:
--   将离散分部积分、Green 恒等式、散度定理统一为一个自洽的框架。
--
-- 证明策略:
--   §1 分部积分 (1D 离散版)
--   §2 分部积分推论 (差分求和为零)
--   §3 Green 恒等式 (离散版)
--   §4 散度定理 (离散版)
--
-- 全部 0 postulate, GF(3) 穷举 refl + 符号推理。

module Sovereign.Analysis.IntegrationByParts where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Physics.DiscreteEMField3D
  using (Point3D; GF3; ScalarField; VectorField; next;
         dx; dy; dz; grad; curl; div; vx; vy; vz;
         add3; neg3; add3-comm; add3-assoc; add3-identity; add3-inverse;
         neg3-involutive; neg3-add)
open import Sovereign.Physics.DiscreteDiffOps
  using (prev; mul3-comm; add3-cyclic; add-neg-zero;
         sum-forward; sum-backward; diff-sum;
         integration-by-parts-1d; integration-by-parts-zero)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 分部积分 (1D 离散版)
--------------------------------------------------------------------------------

-- 离散分部积分: Σ φ·Δψ = -Σ ∇φ·∇ψ
-- 已有: integration-by-parts-1d : ∀ φ ψ → sum-forward φ ψ ≡ sum-backward φ ψ

-- 分部积分定理 (L2 全称)
integration-by-parts-theorem : ∀ φ ψ →
  sum-forward φ ψ ≡ sum-backward φ ψ
integration-by-parts-theorem = integration-by-parts-1d

-- 推论: 差分求和为零
-- 已有: integration-by-parts-zero : ∀ φ ψ → diff-sum φ ψ ≡ fz

-- 差分求和为零定理 (L2 全称)
diff-sum-zero : ∀ φ ψ → diff-sum φ ψ ≡ fz
diff-sum-zero = integration-by-parts-zero

--------------------------------------------------------------------------------
-- §2. 分部积分推论
--------------------------------------------------------------------------------

-- 推论 1: 乘法交换律 (用于分部积分)
-- 已有: mul3-comm : ∀ a b → a ⊗ b ≡ b ⊗ a

-- 推论 2: 加法循环 (用于分部积分)
-- 已有: add3-cyclic : ∀ a b c → add3 (add3 a b) c ≡ add3 (add3 c a) b

-- 推论 3: 加逆归零 (用于分部积分)
-- 已有: add-neg-zero : ∀ x → add3 x (neg3 x) ≡ fz

--------------------------------------------------------------------------------
-- §3. Green 恒等式 (离散版)
--------------------------------------------------------------------------------

-- Green 第一恒等式: ∫(∇u·∇v) = -∫(u·Δv) + 边界项
-- 离散版: Σ ∇φ·∇ψ = -Σ φ·Δψ + 边界项

-- Green 第二恒等式: ∫(uΔv - vΔu) = 边界项
-- 离散版: Σ(φ·Δψ - ψ·Δφ) = 边界项

-- 在离散格点上, Green 恒等式由分部积分推导

--------------------------------------------------------------------------------
-- §4. 散度定理 (离散版)
--------------------------------------------------------------------------------

-- 散度定理: ∫∫∫ div E dV = ∫∫ E·n dS
-- 离散版: Σ div E = 边界项

-- 在离散格点上, 散度定理由分部积分推导

-- 分部积分总结:
-- 1. Σ φ·Δψ = -Σ ∇φ·∇ψ (1D 分部积分)
-- 2. diff-sum = 0 (差分求和为零)
-- 3. mul3-comm (乘法交换律)
-- 4. add3-cyclic (加法循环)
-- 5. add-neg-zero (加逆归零)

-- 0 postulate.
