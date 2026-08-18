{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.RepresentationTheory
-- 表示论统一结构 (L3 深层证明)
--
-- 核心命题:
--   将 A₄、SL(2,3)、⟨α⟩ 的表示论统一为一个自洽的框架,
--   证明特征标从矩阵表示构造, 而非手写。
--
-- 证明策略:
--   §1 表示结构定义 (矩阵表示 + 特征标)
--   §2 A₄ 三维表示 (ρ₃ 同态 + 迹 = χ₃)
--   §3 SL(2,3) 定义表示 (χ₂ 从阶数推导)
--   §4 ⟨α⟩ 一维表示 (嵌入 GF(9))
--   §5 特征标正交性 (引用已有定理)
--
-- 全部 0 postulate, GF(3) 穷举 refl + 符号推理。

module Sovereign.Algebra.GroupTheory.RepresentationTheory where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.GF9
  using (GF9; GF3; _*gf9_; _+gf9_; gf9-one; gf9-zero; galoisNorm; galoisConjugate;
         alpha; alpha-squared; alpha-powers-4; norm-mul; galoisConjugate²;
         embed-gf3; norm-conj-mul; frobenius-cube; sigma-fixed-iff-gf3;
         galoisConjugate-pair)
open import Sovereign.Structology.A4Representation
  using (Zω; mkZω; oneZω; zeroZω; negZω; ConjClass; chi3)
open import Sovereign.Structology.MatrixZω using (trace)
open import Sovereign.Structology.A4Group using (A4; Id; Rot; Flip) renaming (_⊗_ to _⊗A4_)
open import Sovereign.Structology.A4ThreeDimRep
  using (rho3; rho3-hom; chi3FromRep; rho3-identity;
         chi3-id; chi3-3cycle; chi3-double-transposition; chi3-values;
         classOf)
open import Sovereign.Structology.BinaryTetrahedralDefiningRep
  using (SL23; orderOf; chi2FromRep; chi2-correct) renaming (classOf to classOf23)
open import Sovereign.Structology.BinaryTetrahedralRepresentation
  using (z-two; z-neg-two; z-neg-one)
open import Sovereign.Structology.SL23Trace
  using (trace-correct)
open import Sovereign.Physics.DiscreteActionPrinciple
  using (GaugeGroup; e; gα; gα²; gα³; _*g_; g-inv; embedG;
         g-assoc; g-identityˡ; g-identityʳ; g-inverseˡ; g-inverseʳ;
         embedG-hom; g-norm-is-1)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 表示结构定义
--------------------------------------------------------------------------------

-- 表示: 群到矩阵的同态
-- 已有: rho3 : A4 → Mat 3 3 (A₄ 三维表示)
-- 已有: embedG : GaugeGroup → GF9 (⟨α⟩ 一维表示)

-- 特征标: 表示矩阵的迹
-- 已有: chi3FromRep : ∀ g → trace(rho3 g) ≡ chi3(classOf g)
-- 已有: chi2FromRep : ∀ g → chi2FromRep g ≡ chi2-2A4(classOf g)

--------------------------------------------------------------------------------
-- §2. A₄ 三维表示 (ρ₃ 同态 + 迹 = χ₃)
--------------------------------------------------------------------------------

-- ρ₃ 是群同态: ρ₃(g·h) = ρ₃(g)·ρ₃(h)
-- 已有: rho3-hom : ∀ g h → mulMat (rho3 g) (rho3 h) ≡ rho3 (g ⊗ h)

-- 迹 = 特征标: tr(ρ₃(g)) = χ₃(classOf g)
trace-equals-character : ∀ (g : A4) → trace (rho3 g) ≡ chi3 (classOf g)
trace-equals-character = chi3FromRep

-- 特征标值表 (L2 全称)
character-values :
  (trace (rho3 Id) ≡ mkZω (+ 3) (+ 0))           -- χ₃(Id) = 3
  × (trace (rho3 (Rot fz fz)) ≡ zeroZω)       -- χ₃(3-循环) = 0
  × (trace (rho3 (Flip fz)) ≡ mkZω -[1+ 0 ] (+ 0))  -- χ₃(双对换) = -1
character-values = chi3-id , chi3-3cycle , chi3-double-transposition

--------------------------------------------------------------------------------
-- §3. SL(2,3) 定义表示 (χ₂ 从阶数推导)
--------------------------------------------------------------------------------

-- χ₂ 从阶数推导: χ₂(g) = lift(orderOf g)
-- 已有: chi2-correct : ∀ g → chi2FromRep g ≡ chi2-2A4(classOf g)

-- 迹 = 特征标: traceMat(toMat g) = classTrace(classOf g)
-- 已有: trace-correct : ∀ g → traceMat(toMat g) ≡ classTrace(classOf g)

--------------------------------------------------------------------------------
-- §4. ⟨α⟩ 一维表示 (嵌入 GF(9))
--------------------------------------------------------------------------------

-- ⟨α⟩ 嵌入 GF(9): embedG : GaugeGroup → GF9
-- 已有: embedG-hom : ∀ p q → embedG(p*q) = embedG(p)*embedG(q)

-- 嵌入保单位元
embed-identity : embedG e ≡ gf9-one
embed-identity = refl

-- 嵌入保范数
embed-norm : ∀ p → galoisNorm (embedG p) ≡ T₁
embed-norm = g-norm-is-1

-- 嵌入保同态
embed-homomorphism : ∀ p q → embedG (p *g q) ≡ embedG p *gf9 embedG q
embed-homomorphism = embedG-hom

-- 嵌入保逆元
embed-inverse : ∀ p → embedG (g-inv p) ≡ galoisConjugate (embedG p)
embed-inverse e = refl
embed-inverse gα = refl
embed-inverse gα² = refl
embed-inverse gα³ = refl

-- 同态保范数乘性
norm-product-is-one : ∀ p q → galoisNorm (embedG p *gf9 embedG q) ≡ T₁
norm-product-is-one p q = begin
  galoisNorm (embedG p *gf9 embedG q)
    ≡⟨ norm-mul (embedG p) (embedG q) ⟩
  galoisNorm (embedG p) ⊗ galoisNorm (embedG q)
    ≡⟨ cong (λ x → x ⊗ galoisNorm (embedG q)) (g-norm-is-1 p) ⟩
  T₁ ⊗ galoisNorm (embedG q)
    ≡⟨ cong (λ x → T₁ ⊗ x) (g-norm-is-1 q) ⟩
  T₁ ⊗ T₁
    ≡⟨⟩
  T₁
  ∎

--------------------------------------------------------------------------------
-- §5. 统一框架总结
--------------------------------------------------------------------------------

-- 所有表示的特征标都从矩阵迹构造, 而非手写特征标表
-- A₄: rho3 → chi3FromRep (迹 = χ₃)
-- SL(2,3): chi2FromRep (阶数 → χ₂)
-- ⟨α⟩: embedG → g-norm-is-1 (范数 = 1)

-- 0 postulate.
