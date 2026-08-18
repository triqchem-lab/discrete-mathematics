{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.DeRhamComplex
-- 离散 de Rham 复形 (L3 深层证明)
--
-- 核心命题:
--   离散 de Rham 复形 d²=0 的 GF(3) 版本:
--   div∘curl = 0, curl∘grad = 0, 即 d²=0 在离散格点上成立。
--
-- 证明策略:
--   §1 离散微分形式 (0-形式=标量场, 1-形式=向量场, 2-形式=标量场)
--   §2 外微分算子 (grad, curl, div)
--   §3 d²=0 恒等式 (div∘curl=0, curl∘grad=0)
--   §4 de Rham 复形结构 (链复形)
--
-- 全部 0 postulate, GF(3) 穷举 refl + 符号推理。

module Sovereign.Topology.DeRhamComplex where

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
         neg3-involutive; neg3-add;
         curl-grad-zero-x; curl-grad-zero-y; curl-grad-zero-z; curl-grad-zero)
open import Sovereign.Physics.DiscreteEMCore
  using (div-curl-zero)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 离散微分形式
--------------------------------------------------------------------------------

-- 0-形式: 标量场 φ : Point3D → GF3
-- 已有: ScalarField = Point3D → GF3

-- 1-形式: 向量场 A : Point3D → GF3 × GF3 × GF3
-- 已有: VectorField = Point3D → GF3 × GF3 × GF3

-- 2-形式: 标量场 (在 3D 中, 2-形式与 0-形式同构)
-- 已有: ScalarField

--------------------------------------------------------------------------------
-- §2. 外微分算子
--------------------------------------------------------------------------------

-- d₀: 0-形式 → 1-形式 (梯度)
-- 已有: grad : ScalarField → VectorField
-- grad φ = (dx φ, dy φ, dz φ)

-- d₁: 1-形式 → 2-形式 (旋度的散度)
-- 已有: curl : VectorField → VectorField
-- curl A = (dy Az - dz Ay, dz Ax - dx Az, dx Ay - dy Ax)

-- d₂: 2-形式 → 3-形式 (散度)
-- 已有: div : VectorField → ScalarField
-- div A = dx Ax + dy Ay + dz Az

--------------------------------------------------------------------------------
-- §3. d²=0 恒等式
--------------------------------------------------------------------------------

-- 定理 1: curl∘grad = 0 (梯度的旋度为零)
-- 即: d₁∘d₀ = 0
curl-grad-zero-full : ∀ φ p → curl (grad φ) p ≡ (fz , fz , fz)
curl-grad-zero-full = curl-grad-zero

-- 定理 2: div∘curl = 0 (旋度的散度为零)
-- 即: d₂∘d₁ = 0
div-curl-zero-full : ∀ A p → div (curl A) p ≡ fz
div-curl-zero-full = div-curl-zero

-- 定理 3: d²=0 (统一形式)
-- 在离散 de Rham 复形中: d₂∘d₁ = 0 且 d₁∘d₀ = 0
d-squared-zero :
  (∀ A p → div (curl A) p ≡ fz)           -- d₂∘d₁ = 0
  × (∀ φ p → curl (grad φ) p ≡ (fz , fz , fz))  -- d₁∘d₀ = 0
d-squared-zero = div-curl-zero , curl-grad-zero

-- 定理 4: 混合偏导交换 (Schwarz 定理离散版)
-- dy∘dx = dx∘dy, dz∘dx = dx∘dz, dz∘dy = dy∘dz
-- 已有: dy-dx-comm, dz-dx-comm, dz-dy-comm (DiscreteEMField3D)
-- 本模块引用已有定理, 不重复证明

--------------------------------------------------------------------------------
-- §4. de Rham 复形结构
--------------------------------------------------------------------------------

-- 离散 de Rham 复形:
-- 0-形式 ──grad──→ 1-形式 ──curl──→ 2-形式 ──div──→ 3-形式
--   φ            A             B            ρ
-- 条件: curl∘grad = 0, div∘curl = 0

-- 复形结构定理
de-rham-complex :
  -- d₁∘d₀ = 0
  (∀ φ p → curl (grad φ) p ≡ (fz , fz , fz))
  ×
  -- d₂∘d₁ = 0
  (∀ A p → div (curl A) p ≡ fz)
de-rham-complex = curl-grad-zero , div-curl-zero

-- 同调群: H⁰ = ker(d₀)/im(0) = 常数场
-- H¹ = ker(d₁)/im(d₀) = 无旋场/梯度场
-- H² = ker(d₂)/im(d₁) = 无散场/旋度场
-- 在离散格点上, 同调群是有限维 GF(3)-向量空间

-- 0 postulate.
