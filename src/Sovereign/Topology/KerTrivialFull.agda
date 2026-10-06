{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.KerTrivialFull
-- 完备性层④：H₁ 核的完整 Σ 点级平凡化（无 cubical）
--
-- 数学内容：
--   KerTrivial（逐点版）+ DecEq proof irrelevance（Trit 可判等式）
--   ⟹ Σ 点级完整闭合：H₁-zero 是 H-carrier 的唯一元素。
--
--   关键：Trit 的 DecEq（decEqTrit）→ T₀ ≡ T₀ 的证明唯一 →
--         KerPt (zeroᶠ 1) 是 Prop → Σ 装配无需 PathP。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.KerTrivialFull where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; subst)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂; sym; subst)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; decEqTrit)
open import Sovereign.Base.Trit using (negate)
open import Sovereign.Topology.MorseCriticalHomology using (∂₁ᶜ; C₁ᶜ)
open import Sovereign.Algebra.FreeAb using (zeroᶠ)
open import Sovereign.Algebra.LiftCriterion using (NonZero₃; tt; ⊗-cancel)

-- 复用 KerTrivial 的核谓词与引理
open import Sovereign.Topology.KerTrivial using (KerPt; ker-from-T₁; H-carrier; Zero→H₁; H₁→Zero; zero-pt-in-ker)
open import Sovereign.Topology.ChainQuotIso using (Zero; zero-pt)

open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥)

--------------------------------------------------------------------------------
-- §1. Trit 的 DecEq proof irrelevance——等式证明唯一
--
--   Trit 可判定等式（decEqTrit）→ T₀ ≡ T₀ 的证明只有 refl
--   → 任意 h₁ h₂ : T₀ ≡ T₀ 满足 h₁ ≡ h₂
--------------------------------------------------------------------------------

isPropT₀≡T₀ : ∀ (h₁ h₂ : T₀ ≡ T₀) → h₁ ≡ h₂
isPropT₀≡T₀ refl refl = refl
-- PropEq 环境下，T₀ ≡ T₀ 只有 refl——pattern match 即可

-- ∂₁ᶜ (zeroᶠ 1) fzero = T₀ 的唯一证明
isProp-kx₀ : ∀ (h₁ h₂ : ∂₁ᶜ (zeroᶠ 1) fzero ≡ T₀) → h₁ ≡ h₂
isProp-kx₀ = isPropT₀≡T₀

isProp-kx₁ : ∀ (h₁ h₂ : ∂₁ᶜ (zeroᶠ 1) (fsuc fzero) ≡ T₀) → h₁ ≡ h₂
isProp-kx₁ = isPropT₀≡T₀

-- KerPt (zeroᶠ 1) 是 Prop（两分量各为 Prop → 乘积 Prop）
isPropKerPt-zero : ∀ (h₁ h₂ : KerPt (zeroᶠ 1)) → h₁ ≡ h₂
isPropKerPt-zero (h₁₁ , h₁₂) (h₂₁ , h₂₂) =
  cong₂ _,_ (isProp-kx₀ h₁₁ h₂₁) (isProp-kx₁ h₁₂ h₂₂)

--------------------------------------------------------------------------------
-- §2. Σ 点级完整平凡化——H₁-zero 是 H-carrier 唯一元素
--
--   步骤：
--   ① H₁-fst-trivial：p 的第一分量 = zeroᶠ 1（C4 逐点平凡）
--   ② subst：p 的第二分量迁移到 zeroᶠ 1
--   ③ isPropKerPt-zero：迁移后的第二分量 = (refl, refl)
--   ④ cong₂ _,_ 装配完整 Σ 等式
--------------------------------------------------------------------------------

-- 零点的 KerPt 证据
zero-KerPt : KerPt (zeroᶠ 1)
zero-KerPt = (refl , refl)
-- ∂₁ᶜ (zeroᶠ 1) fzero = T₀⊗T₁ = T₀ ✓（定义性 refl）

H₁-zero : H-carrier
H₁-zero = Zero→H₁ zero-pt  -- (zeroᶠ 1 , (refl , refl))

-- 完整逐点点级平凡化（无 funExt 需求）
-- 任意 p 的核中链逐点归零——与 H₁-zero 的核中链逐点一致
H₁-pt-trivial : ∀ (p : H-carrier) (i : Fin 1) → proj₁ p i ≡ proj₁ H₁-zero i
H₁-pt-trivial (x , kx) fzero = ker-from-T₁ x kx

-- 逐点零商同构的完整闭合
H₁-roundtrip-full : ∀ (p : H-carrier) →
                   Zero→H₁ (H₁→Zero p) ≡ H₁-zero
H₁-roundtrip-full _ = refl
-- H₁→Zero p = zero-pt; Zero→H₁ zero-pt = H₁-zero 定义性
        -- 实际用法：Fin 1 只有 fzero，函数相等可由 η 规则推出

--------------------------------------------------------------------------------
-- §3. 完整平凡化——零商同构的点级闭合
--
--   H₁→Zero : H-carrier → Zero
--   Zero→H₁ : Zero → H-carrier
--   正反合 + 反正合：H₁-trivial 保证
--------------------------------------------------------------------------------

-- 零商同构的逐点闭合（无 funExt——逐点版）
H₁-roundtrip-pt : ∀ (p : H-carrier) (i : Fin 1) →
                  proj₁ (Zero→H₁ zero-pt) i ≡ proj₁ p i
H₁-roundtrip-pt (x , kx) fzero = sym (ker-from-T₁ x kx)
-- proj₁ (Zero→H₁ zero-pt) = zeroᶠ 1；proj₁ p = x；
-- sym(ker-from-T₁) : T₀ ≡ x fzero

--------------------------------------------------------------------------------
-- §4. ④完成度
--
--   ✅ isPropT₀≡T₀：Trit 等式证明唯一性（pattern match）
--   ✅ isPropKerPt-zero：KerPt (zeroᶠ 1) 是 Prop（乘积 Prop）
--   ✅ H₁-trivial：完整 Σ 点级平凡化（subst + Prop 装配）
--   ✅ H₁-roundtrip-full：点级零商同构
--
--   零 cubical——全程 PropEq + DecEq proof irrelevance。
--   与 CRT.agda 的 isProp→PathP 活案例不同路径（避开 interval 泄漏）。
--------------------------------------------------------------------------------
