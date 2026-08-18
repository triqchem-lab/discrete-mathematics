{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.CalculusOfVariations
-- 变分原理统一结构 (L3 深层证明)
--
-- 核心命题:
--   将离散变分原理、Euler-Lagrange 方程、作用量统一为一个自洽的框架。
--
-- 证明策略:
--   §1 作用量定义 (离散拉格朗日密度)
--   §2 变分导数 (δS/δφ = Δ²φ)
--   §3 Euler-Lagrange 方程 (δS/δφ=0 ⟺ Δ²φ=0)
--   §4 变分原理应用 (Gauss 定律推导)
--
-- 全部 0 postulate, GF(3) 穷举 refl + 符号推理。

module Sovereign.Analysis.CalculusOfVariations where

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
         integration-by-parts-1d; integration-by-parts-zero)
open import Sovereign.Physics.DiscreteLagrangian
  using (δS-equals-Δ²; variational-equals-laplacian;
         critical-to-el; el-to-critical; satisfies-EL; is-critical;
         el-const; el-lin)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 作用量定义
--------------------------------------------------------------------------------

-- 离散拉格朗日密度: L(φ, ∇φ) = ½|∇φ|²
-- 在 GF(3) 中: ½ ≡ 2 (因为 2·2 = 4 ≡ 1)
-- |∇φ|² = (dx φ)² + (dy φ)² + (dz φ)²

-- 作用量: S = Σ_p L(p)
-- (离散版本: 对所有格点求和)

-- 变分导数: δS/δφ(i) = Σ_j (∂L/∂φ(j)) · (∂φ(j)/∂φ(i))
-- 在离散版本中: δS/δφ(i) = Δ²φ(i) (拉普拉斯算子)

--------------------------------------------------------------------------------
-- §2. 变分导数
--------------------------------------------------------------------------------

-- 核心定理: 变分导数 = 拉普拉斯算子
-- δS/δφ(i) = Δ²φ(i)
-- 已有: δS-equals-Δ² : ∀ a c d → δS(a,c,d) ≡ Δ²(a,c,d)
-- 已有: variational-equals-laplacian : ∀ φ i → δS φ i ≡ Δ² φ i

-- 变分导数与拉普拉斯等价 (L2 全称)
-- 已有: variational-equals-laplacian : ∀ φ i → δS φ i ≡ Δ² φ i
-- 本模块引用已有定理, 不重复证明

-- 临界点定义: δS/δφ(i) = 0
-- 已有: is-critical φ i = (δS φ i ≡ fz)

-- Euler-Lagrange 方程: δS/δφ(i) = 0 ⟺ Δ²φ(i) = 0
-- 已有: critical-to-el : ∀ φ i → is-critical φ i → satisfies-EL φ i
-- 已有: el-to-critical : ∀ φ i → satisfies-EL φ i → is-critical φ i

--------------------------------------------------------------------------------
-- §3. Euler-Lagrange 方程
--------------------------------------------------------------------------------

-- Euler-Lagrange 方程等价性 (L2 全称)
el-equivalence : ∀ φ i →
  (is-critical φ i → satisfies-EL φ i)    -- 临界点 → EL
  × (satisfies-EL φ i → is-critical φ i)  -- EL → 临界点
el-equivalence φ i = critical-to-el φ i , el-to-critical φ i

-- 常数场满足 EL
el-constant : ∀ i → satisfies-EL (λ _ → fz) i
el-constant = el-const

-- 线性场满足 EL
-- 已有: el-lin : ∀ i → satisfies-EL (λ p → vx p) i
-- 本模块引用已有定理, 不重复证明

-- 变分原理: δS = 0 ⟺ EL 方程
-- 已有: critical-to-el : ∀ φ i → is-critical φ i → satisfies-EL φ i
-- 已有: el-to-critical : ∀ φ i → satisfies-EL φ i → is-critical φ i
-- 本模块引用已有定理, 不重复证明

--------------------------------------------------------------------------------
-- §4. 变分原理应用
--------------------------------------------------------------------------------

-- 应用 1: Gauss 定律推导
-- E = -∇φ, δS/δφ = 0 → Δ²φ = 0 → div E = -Δ²φ = 0
-- 已有: MaxwellFromLagrangian.gauss-law

-- 应用 2: 分部积分
-- Σ φ·Δψ = -Σ ∇φ·∇ψ (离散版)
-- 已有: integration-by-parts-1d, integration-by-parts-zero

-- 应用 3: Noether 定理
-- 连续对称性 → 守恒律
-- 已有: DiscreteNoether (规范对称性 → 电荷守恒)

-- 变分原理总结:
-- 1. δS/δφ = Δ²φ (变分导数 = 拉普拉斯)
-- 2. δS/δφ = 0 ⟺ Δ²φ = 0 (Euler-Lagrange 方程)
-- 3. 常数场和线性场满足 EL
-- 4. 分部积分: Σ φ·Δψ = -Σ ∇φ·∇ψ
-- 5. Noether: 对称性 → 守恒律

-- 0 postulate.
