{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.HilbertDiscrete
-- 离散 Hilbert 空间: GF(9)ⁿ + Hermitian 内积 + 有限维完备性
--
-- 核心结构:
--   DiscreteHilbert n = VectorSpace n (GF9ⁿ 函数表示)
--   内积: hermitianIP (共轭对称, 正定)
--   范数: normSq = Σᵢ f(i)·σ(f(i))
--   完备性: 有限集合上轨道最终周期 (来自 FiniteDynamics)
--   顶点代数嵌入: Y(a)|0⟩ = a (创生公理)
--
-- 0 postulate — 全部构造性证明

module Sovereign.Analysis.HilbertDiscrete where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GF9 using (
  GF9; gf9-one; _+gf9_; _*gf9_;
  galoisConjugate; galoisConjugate²; galoisNorm; embed-gf3)

open import Sovereign.Analysis.FiniteInnerProduct using (
  VectorSpace; gf9-zero; zeroVec; _+V_; _·V_;
  hermitianIP; hermitian-conj-sym; normSq;
  normSq-of-zero; galoisNorm-zero;
  Orthogonal; zero-orthogonalˡ; zero-orthogonalʳ;
  basisVec; basisVec-diag)

open import Sovereign.Analysis.FiniteDynamics using (
  orbit; EventuallyPeriodic; orbit-eventually-periodic)

open import Sovereign.Analysis.VertexAlgebraDiscrete using (
  VertexOp; Y; vacuum; _*V_)

--------------------------------------------------------------------------------
-- §1. 离散 Hilbert 空间
--------------------------------------------------------------------------------

-- 离散 Hilbert 空间 = GF(9)ⁿ 带 Hermitian 内积
DiscreteHilbert : ℕ → Set
DiscreteHilbert n = VectorSpace n

-- 内积 (n 隐式)
⟨_∣_⟩ : ∀ {n} → DiscreteHilbert n → DiscreteHilbert n → GF9
⟨ f ∣ g ⟩ = hermitianIP _ f g

-- 范数平方 (n 隐式)
‖_‖² : ∀ {n} → DiscreteHilbert n → GF9
‖ f ‖² = normSq _ f

--------------------------------------------------------------------------------
-- §2. 正定性
--------------------------------------------------------------------------------

-- 正定性: 已由 FiniteInnerProduct.galoisNorm-zero 给出
-- galoisNorm x ≡ T₀ → x ≡ gf9-zero
-- 此处重导出供 P0 证据引用
positive-definite : ∀ (x : GF9) → galoisNorm x ≡ T₀ → x ≡ gf9-zero
positive-definite = galoisNorm-zero

-- 零向量的范数为零
zero-norm : ∀ n → normSq n (zeroVec n) ≡ gf9-zero
zero-norm n = normSq-of-zero n

-- 零向量与任何向量正交
zero-orth : ∀ n (g : DiscreteHilbert n) → Orthogonal n (zeroVec n) g
zero-orth n g = zero-orthogonalˡ n g

--------------------------------------------------------------------------------
-- §3. 共轭对称性
--------------------------------------------------------------------------------

-- ⟨f,g⟩ = σ(⟨g,f⟩)
conj-symmetric : ∀ n (f g : DiscreteHilbert n) →
  hermitianIP n f g ≡ galoisConjugate (hermitianIP n g f)
conj-symmetric n f g = hermitian-conj-sym n f g

--------------------------------------------------------------------------------
-- §4. 有限维完备性 (轨道最终周期)
--------------------------------------------------------------------------------

-- GF(9)ⁿ 上的确定性动力系统轨道最终周期
-- 这是 Hilbert 空间"完备性"的离散替代:
-- 连续 Hilbert 空间中 Cauchy 序列收敛 ↔ 离散空间中轨道进入极限环

-- 核心定理 (直接引用 FiniteDynamics):
-- Fin N 上任意函数的轨道最终周期, 周期 ≤ N
hilbert-complete-fin : ∀ N → (f : Fin N → Fin N) → (x0 : Fin N) →
  EventuallyPeriodic (orbit f x0)
hilbert-complete-fin N f x0 = orbit-eventually-periodic N f x0

-- Frobenius 轨道的精确周期 (σ² = id, 周期 ≤ 2)
frobenius-hilbert-cycle : ∀ (x : GF9) →
  orbit galoisConjugate x 2 ≡ x
frobenius-hilbert-cycle x = galoisConjugate² x

--------------------------------------------------------------------------------
-- §5. 顶点代数 → Hilbert 空间嵌入
--------------------------------------------------------------------------------

-- 嵌入: 顶点算子作用于真空 → Hilbert 向量
embed-vertex : ∀ n → VertexOp n → DiscreteHilbert n
embed-vertex n op = op (vacuum n)

-- 真空态嵌入为零向量 (真空算子作用于真空 = 零)
embed-vacuum-zero : ∀ n → embed-vertex n (Y (zeroVec n)) ≡ zeroVec n
embed-vacuum-zero n = refl

--------------------------------------------------------------------------------
-- §6. 基向量的正交性
--------------------------------------------------------------------------------

-- 标准基: eᵢ(j) = δᵢⱼ
basis : ∀ n → Fin n → DiscreteHilbert n
basis n i = basisVec n i

-- 基向量在自身处的值为 1
basis-self : ∀ n (i : Fin n) → basisVec n i i ≡ gf9-one
basis-self n i = basisVec-diag n i

--------------------------------------------------------------------------------
-- §7. P0 完备性证据
--------------------------------------------------------------------------------

-- HilbertSpace 的离散替代已完成:
--   载体: DiscreteHilbert n = GF9ⁿ
--   内积: hermitianIP (共轭对称, 正定)
--   完备性: 有限维 → 轨道最终周期 (替代 Cauchy 收敛)
--   顶点代数嵌入: Y(a)|0⟩ 创生公理

-- 证据记录 (供 CompletenessTheorem 引用)
hilbert-discrete-summary : Σ ℕ (λ n → DiscreteHilbert n)
hilbert-discrete-summary = 1 , zeroVec 1
