{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Quantum.NoCloning
-- qutrit 不可克隆定理 — Z[ω] 系数精确版 (0 postulate)
--
-- 诚实边界 (关键):
--   纯 GF(3) 系数下, 对角线映射 ψ ↦ ψ⊗ψ 是线性的 — (x⊕y)⊗(x⊕y) 的分量
--   逐位 = x⊕y, 特征 3 不产生存活交叉项, 故"线性 ⟹ 不可克隆"在 GF(3)
--   上是假定理。真正的量子不可克隆的离散载体是 Z[ω] (艾森斯坦整数,
--   项目的精确复数层): 叠加态 |0⟩+|1⟩ 的克隆要求交叉项 |01⟩ 系数为 1,
--   而线性性只给出 0 — 在整数环 Z[ω] 中 0 ≢ 1, 矛盾。
--
-- 结构:
--   §1 Z[ω] 二能级子空间 QE2 = Z[ω]², 张量积 QE4 = Z[ω]⁴
--   §2 克隆电路协议: 线性 + 酉性 (保范) + CloningCircuit
--   §3 主定理: 不存在线性+酉的克隆电路 (矛盾仅由线性导出,
--      酉性是物理前提, 不进入矛盾链 — 与标准证明一致)

module Sovereign.Quantum.NoCloning where

open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; module ≡-Reasoning)
open ≡-Reasoning

import Sovereign.RootMath.Eisenstein as Eis

--------------------------------------------------------------------------------
-- §1. Z[ω] 态空间与张量积
--------------------------------------------------------------------------------

-- 二能级子空间 (qutrit 计算基 |0⟩, |1⟩ 子空间): (a, b) = a|0⟩ + b|1⟩
QE2 : Set
QE2 = Eis.Eisenstein × Eis.Eisenstein

-- 双粒子空间: (a, b, c, d) = a|00⟩ + b|01⟩ + c|10⟩ + d|11⟩
QE4 : Set
QE4 = Eis.Eisenstein × Eis.Eisenstein × Eis.Eisenstein × Eis.Eisenstein

ket0E : QE2
ket0E = Eis.1ᵉ , Eis.0ᵉ

ket1E : QE2
ket1E = Eis.0ᵉ , Eis.1ᵉ

-- 叠加态 ψ = |0⟩ + |1⟩ = (1, 1) — 不可克隆的见证
psiE : QE2
psiE = Eis.1ᵉ , Eis.1ᵉ

-- 分量加法 (QE2 / QE4)
_+E_ : QE2 → QE2 → QE2
(a , b) +E (c , d) = (a Eis.+ᵉ c) , (b Eis.+ᵉ d)

_+E4_ : QE4 → QE4 → QE4
(a , b , c , d) +E4 (e , f , g , h) =
  (a Eis.+ᵉ e) , (b Eis.+ᵉ f) , (c Eis.+ᵉ g) , (d Eis.+ᵉ h)

-- 张量积: (a,b)⊗(c,d) = (ac, ad, bc, bd)
_⊗E_ : QE2 → QE2 → QE4
(a , b) ⊗E (c , d) =
  (a Eis.*ᵉ c) , (a Eis.*ᵉ d) , (b Eis.*ᵉ c) , (b Eis.*ᵉ d)

-- |01⟩ 分量投影
comp2 : QE4 → Eis.Eisenstein
comp2 (_ , b , _ , _) = b

--------------------------------------------------------------------------------
-- §2. 克隆电路协议: 线性 + 酉性 (保范) + 克隆要求
--------------------------------------------------------------------------------

-- 线性 (可加性 — 矛盾链仅消耗此条)
IsLinear4 : (QE4 → QE4) → Set
IsLinear4 U = ∀ x y → U (x +E4 y) ≡ U x +E4 U y

-- 范数平方 (Z[ω] 精确版): ⟨ψ|ψ⟩ = Σ conj(xᵢ)·xᵢ
norm4 : QE4 → Eis.Eisenstein
norm4 (a , b , c , d) =
  (Eis.conjᵉ a Eis.*ᵉ a) Eis.+ᵉ (Eis.conjᵉ b Eis.*ᵉ b)
  Eis.+ᵉ (Eis.conjᵉ c Eis.*ᵉ c) Eis.+ᵉ (Eis.conjᵉ d Eis.*ᵉ d)

-- 酉性 = 保范 (离散精确版; 酉演化保持 Z[ω] 范数)
IsUnitary4 : (QE4 → QE4) → Set
IsUnitary4 U = ∀ x → norm4 (U x) ≡ norm4 x

-- 克隆电路协议: U(ψ ⊗ |0⟩) = ψ ⊗ ψ
CloningCircuit : (QE4 → QE4) → Set
CloningCircuit U = ∀ ψ → U (ψ ⊗E ket0E) ≡ ψ ⊗E ψ

--------------------------------------------------------------------------------
-- §3. 主定理: 不存在线性 + 酉的克隆电路
--------------------------------------------------------------------------------

-- Z[ω] 的整数性: 0 ≢ 1 (构造子 eis (+0)(+0) 与 eis (+1)(+0) 不同)
eis-0≢1 : ¬ (Eis.0ᵉ ≡ Eis.1ᵉ)
eis-0≢1 ()

-- 线性性给出的 |01⟩ 分量 = 0:
--   U(ψ⊗|0⟩) = U((|0⟩⊗|0⟩) + (|1⟩⊗|0⟩)) = |0⟩|0⟩ + |1⟩|1⟩ (线性)
--   → comp2 = 0
linear-branch : ∀ (U : QE4 → QE4) → IsLinear4 U → CloningCircuit U →
  comp2 (U (psiE ⊗E ket0E)) ≡ Eis.0ᵉ
linear-branch U lin cl = begin
  comp2 (U (psiE ⊗E ket0E))
    ≡⟨ cong comp2 (lin (ket0E ⊗E ket0E) (ket1E ⊗E ket0E)) ⟩
  comp2 (U (ket0E ⊗E ket0E) +E4 U (ket1E ⊗E ket0E))
    ≡⟨ cong comp2 (cong₂ _+E4_ (cl ket0E) (cl ket1E)) ⟩
  comp2 ((ket0E ⊗E ket0E) +E4 (ket1E ⊗E ket1E))
    ≡⟨ refl ⟩
  Eis.0ᵉ ∎

-- 克隆要求给出的 |01⟩ 分量 = 1: U(ψ⊗|0⟩) = ψ⊗ψ = (1,1,1,1) → comp2 = 1
clone-branch : ∀ (U : QE4 → QE4) → CloningCircuit U →
  comp2 (U (psiE ⊗E ket0E)) ≡ Eis.1ᵉ
clone-branch U cl = begin
  comp2 (U (psiE ⊗E ket0E))
    ≡⟨ cong comp2 (cl psiE) ⟩
  comp2 (psiE ⊗E psiE)
    ≡⟨ refl ⟩
  Eis.1ᵉ ∎

-- 主定理: 线性 + 酉性 + 克隆要求 ⟹ 矛盾 (0 ≢ 1)
-- (酉性在陈述中作为物理前提; 矛盾链只消耗线性 — 与标准证明一致)
no-cloning-circuit :
  ¬ Σ (QE4 → QE4) (λ U → IsLinear4 U × IsUnitary4 U × CloningCircuit U)
no-cloning-circuit (U , lin , uni , cl) = eis-0≢1 (begin
  Eis.0ᵉ
    ≡⟨ sym (linear-branch U lin cl) ⟩
  comp2 (U (psiE ⊗E ket0E))
    ≡⟨ clone-branch U cl ⟩
  Eis.1ᵉ ∎)
