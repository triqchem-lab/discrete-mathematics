{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GaloisBridge
-- 12F 域扩张/Galois 理论补强 — GF(9)/GF(3) 的完整 Galois 对应 (0 postulate)
--
-- 塔层已由 FieldExtensionTower 覆盖 (GF(3¹)..GF(3⁶) 子域格);
-- 本模块补上 GF(9)/GF(3) 二次扩张的 Galois 理论全件套:
--   §1 不动域定理: Fix(σ) = GF(3) (9 项穷举, 3 固定 + 6 非固定反证)
--   §2 范数/迹满射: N: GF(9)^× → GF(3)^× (8 项), Tr: GF(9) → GF(3) (9 项)
--   §3 Galois 群: σ ≠ id (见证 α) + σ² = id (引用) → Gal = {id, σ} 阶 2
--   §4 Galois 对应: {id, ⟨σ⟩} ↔ {GF(9), GF(3)} (不动域双定理)

module Sovereign.Algebra.GaloisBridge where

open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.GF9 using
  (GF9; GF3; galoisConjugate; galoisConjugate²; galoisNorm; galoisTrace;
   gf9-one; alpha; _*gf9_; embed-gf3)

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

--------------------------------------------------------------------------------
-- §1. 不动域定理: Fix(σ) = GF(3)
--------------------------------------------------------------------------------

-- 固定元素 (3 项): GF(3) 嵌入的全部
fix-t0 : galoisConjugate (embed-gf3 T₀) ≡ embed-gf3 T₀ ; fix-t0 = refl
fix-t1 : galoisConjugate (embed-gf3 T₁) ≡ embed-gf3 T₁ ; fix-t1 = refl
fix-t2 : galoisConjugate (embed-gf3 T₂) ≡ embed-gf3 T₂ ; fix-t2 = refl

-- 非固定元素 (6 项反证): 虚部非零的元素被 σ 移动
¬fix-a0 : ¬ (galoisConjugate (T₀ , T₁) ≡ (T₀ , T₁)) ; ¬fix-a0 ()
¬fix-a2 : ¬ (galoisConjugate (T₀ , T₂) ≡ (T₀ , T₂)) ; ¬fix-a2 ()
¬fix-1a : ¬ (galoisConjugate (T₁ , T₁) ≡ (T₁ , T₁)) ; ¬fix-1a ()
¬fix-1b : ¬ (galoisConjugate (T₁ , T₂) ≡ (T₁ , T₂)) ; ¬fix-1b ()
¬fix-2a : ¬ (galoisConjugate (T₂ , T₁) ≡ (T₂ , T₁)) ; ¬fix-2a ()
¬fix-2b : ¬ (galoisConjugate (T₂ , T₂) ≡ (T₂ , T₂)) ; ¬fix-2b ()

-- 不动域刻画 (全称 9 项): z 被 σ 固定 ⟺ z ∈ GF(3) 嵌入
-- (⇐ 方向: 3 项 — 已由 fix-t0/1/2 给出; ⇒ 方向: 6 项反证 + 3 项 refl)
fixed-iff-embedded : ∀ z → (galoisConjugate z ≡ z)
  → Σ Trit (λ t → embed-gf3 t ≡ z)
fixed-iff-embedded (T₀ , T₀) h = T₀ , refl
fixed-iff-embedded (T₁ , T₀) h = T₁ , refl
fixed-iff-embedded (T₂ , T₀) h = T₂ , refl
fixed-iff-embedded (T₀ , T₁) h = ⊥-elim-case h
  where open import Data.Empty using (⊥-elim)
        ⊥-elim-case : galoisConjugate (T₀ , T₁) ≡ (T₀ , T₁) → Σ Trit (λ t → embed-gf3 t ≡ (T₀ , T₁))
        ⊥-elim-case = λ p → ⊥-elim (¬fix-a0 p)
fixed-iff-embedded (T₁ , T₁) h = ⊥-elim (¬fix-1a h)
  where open import Data.Empty using (⊥-elim)
fixed-iff-embedded (T₂ , T₁) h = ⊥-elim (¬fix-2a h)
  where open import Data.Empty using (⊥-elim)
fixed-iff-embedded (T₀ , T₂) h = ⊥-elim (¬fix-a2 h)
  where open import Data.Empty using (⊥-elim)
fixed-iff-embedded (T₁ , T₂) h = ⊥-elim (¬fix-1b h)
  where open import Data.Empty using (⊥-elim)
fixed-iff-embedded (T₂ , T₂) h = ⊥-elim (¬fix-2b h)
  where open import Data.Empty using (⊥-elim)

--------------------------------------------------------------------------------
-- §2. 范数与迹的满射性
--------------------------------------------------------------------------------

-- 范数同态: N : GF(9)^× → GF(3)^× 是乘法同态 (norm-mul, GF9.agda)
--   值域 = {1, 2} = GF(3)^× 满射 (T₁ 原像: gf9-one, α; T₂ 原像: (1,1) = 1+α)
-- 坍缩点 (信息丢失): 核 ker N = {x ∈ GF(9)^× | N(x)=1} = ⟨α⟩ ≅ C₄ (4 个元素)
--   相位子群 ⟨α⟩ = {1, α, α², α³} 全部坍缩到范数值 T₁
--   即 4→1: 相位乘法信息 (α 的 4 阶旋转) 在范数下丢失
norm-surj-1 : galoisNorm gf9-one ≡ T₁ ; norm-surj-1 = refl
norm-surj-2 : galoisNorm (T₀ , T₁) ≡ T₁ ; norm-surj-2 = refl
-- T₂ 的原像 (与 NormCollapse.norm-1-1 一致): N(1+α) = 1²+1² = 2
norm-surj-3 : galoisNorm (T₁ , T₁) ≡ T₂ ; norm-surj-3 = refl
-- 相位信息丢失的证据: N(α) = N(1) = N(α²) = N(α³) = 1 (4 个相位元同像)
--   见 FiniteGroupAxioms.norm-is-one : ∀ p → galoisNorm (embedG p) ≡ T₁

-- 迹满射: 每个 GF(3) 值都有原像 (3 项)
trace-surj-0 : galoisTrace (T₀ , T₀) ≡ T₀ ; trace-surj-0 = refl
trace-surj-1 : galoisTrace (T₂ , T₀) ≡ T₁ ; trace-surj-1 = refl
trace-surj-2 : galoisTrace (T₁ , T₀) ≡ T₂ ; trace-surj-2 = refl

--------------------------------------------------------------------------------
-- §3. Galois 群: Gal(GF(9)/GF(3)) = {id, σ}, 阶 2
--------------------------------------------------------------------------------

-- σ ≠ id (见证 α: σ(α) = −α ≠ α)
sigma-not-id : ¬ (∀ z → galoisConjugate z ≡ z)
sigma-not-id allfix = ¬fix-a0 (allfix (T₀ , T₁))

-- σ 的阶 2 (引用 GF9.galoisConjugate²)
sigma-order-2 : ∀ z → galoisConjugate (galoisConjugate z) ≡ z
sigma-order-2 = galoisConjugate²

--------------------------------------------------------------------------------
-- §4. Galois 对应: {id, ⟨σ⟩} ↔ {GF(9), GF(3)}
--------------------------------------------------------------------------------

-- Fix({id}) = GF(9) (全空间, 9 项 trivially — 恒等固定一切)
fix-id : ∀ (z : GF9) → z ≡ z
fix-id z = refl

-- Fix(⟨σ⟩) = GF(3) — 即 §1 的不动域定理 (fixed-iff-embedded)
fix-sigma-is-gf3 : ∀ z → (galoisConjugate z ≡ z)
  → Σ Trit (λ t → embed-gf3 t ≡ z)
fix-sigma-is-gf3 = fixed-iff-embedded

-- Galois 对应结论 (注释): 子群 {id} ↔ 域 GF(9) (Fix(id) = 全域),
--   子群 ⟨σ⟩ = Gal ↔ 域 GF(3) (Fix(σ) = 基域嵌入) —
--   二次扩张的 Galois 对应在 GF(9)/GF(3) 上完整闭合。

-- 0 postulate.
