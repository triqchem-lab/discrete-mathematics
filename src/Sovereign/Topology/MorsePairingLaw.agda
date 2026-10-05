{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorsePairingLaw
-- M3 里程碑 3：匹配结构设计——反例 + 带显式前提的泛型定理
--
-- 计划分水岭裁决：路径 (b)。
--   现有 MorsePartialG 字段不足以推出 ∂²=0——本模块给出构造性反例
--   （3 胞腔 + coeff 全 T₁，twoStepCoeff = T₁ ≠ T₀）。
--   结论：泛型 ∂²=0 需要显式配对互补前提（PairingLaw record 字段，
--   非 postulate——record 假设参数是构造性合法形式）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorsePairingLaw where

open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; ⊕-identityʳ)
open import Sovereign.Topology.MorsePartialG

--------------------------------------------------------------------------------
-- §1. 构造性反例——现有字段不足以推出 ∂²=0
--------------------------------------------------------------------------------

-- 1a. 三胞腔类型：σ（源）、ω（中间）、τ（临界终点）
data C3 : Set where
  cσ cω cτ : C3

-- 1b. 反例实例：coeff cσ cω = T₁、coeff cω cτ = T₁，其余 T₀
coeffEx : C3 → C3 → Trit
coeffEx cσ cω = T₁
coeffEx cω cτ = T₁
coeffEx _  _  = T₀

pgEx : MorsePartialG C3 (λ _ _ → ⊥) (λ _ → nothing)
pgEx = record
  { isCritical = λ _ → ⊥
  ; coeff      = coeffEx
  ; routeList  = λ _ → []
  }

-- 1c. 反例计算：twoStepCoeff pgEx (cω ∷ []) cσ cτ = (T₁ ⊗ T₁) ⊕ T₀ = T₁
F3⊥ : C3 → C3 → Set
F3⊥ = λ _ _ → ⊥

V3∅ : C3 → Maybe C3
V3∅ = λ _ → nothing

ex-sum : TwoStep.twoStepCoeff C3 F3⊥ V3∅ pgEx (cω ∷ []) cσ cτ ≡ T₁
ex-sum = refl

-- 1d. T₁ ≢ T₀（构造子不相交）
neq-T₁-T₀ : ¬ (T₁ ≡ T₀)
neq-T₁-T₀ ()

-- 1e. 反例结论：∂²=0 在此实例上失败
ex-sqzero-fails :
  ¬ (TwoStep.twoStepCoeff C3 F3⊥ V3∅ pgEx (cω ∷ []) cσ cτ ≡ T₀)
ex-sqzero-fails h = neq-T₁-T₀ (trans (sym ex-sum) h)

--------------------------------------------------------------------------------
-- §2. 里程碑 3 裁决——路径 (b)：显式前提（PairingLaw record）
--
--   反例说明：仅凭 coeff 数据，twoStepCoeff 可取任意值。
--   ∂²=0 的代数本质：每个配对中间胞腔 ω 的两条出口路径系数互反。
--   这条「出口互补律」作为显式 record 前提（非 postulate）。
--------------------------------------------------------------------------------

record PairingLaw (K : Set) : Set₁ where
  field
    -- 面出口系数 b(ω,τ) 与 V 出口系数 e'(ω,τ)
    faceExit : K → K → Trit
    vExit    : K → K → Trit
    -- 出口互补律：faceExit ω τ ⊕ vExit ω τ ≡ T₀（对所有 ω τ）
    exit-opp : ∀ (ω τ : K) → faceExit ω τ ⊕ vExit ω τ ≡ T₀

--------------------------------------------------------------------------------
-- §3. 带前提消元引理（完整可证——里程碑 4 的基本步）
--
--   单胞腔两步系数：μ = a ⊗ (b ⊕ e')
--   前提：b ⊕ e' ≡ T₀（出口互补）
--   结论：μ ≡ T₀（a ⊗ T₀ 定义性 = T₀）
--------------------------------------------------------------------------------

oneStepPair : Trit → Trit → Trit → Trit
oneStepPair a b e' = a ⊗ (b ⊕ e')

-- 局部 ⊗-zeroʳ（按 a 三构造子 case——Base/Trit 无此引理，不动 300+ 依赖的根基模块）
⊗-zeroʳ-loc : (a : Trit) → a ⊗ T₀ ≡ T₀
⊗-zeroʳ-loc T₀ = refl
⊗-zeroʳ-loc T₁ = refl
⊗-zeroʳ-loc T₂ = refl

oneStepPair-zero : (a b e' : Trit) → b ⊕ e' ≡ T₀ →
                   oneStepPair a b e' ≡ T₀
oneStepPair-zero a b e' h = trans (cong (λ z → a ⊗ z) h) (⊗-zeroʳ-loc a)

-- 挂到 PairingLaw：单胞腔版定理（ω 的出入系数取自 PairingLaw）
oneStep-zero : (law : PairingLaw ⊤) (a : Trit) (ω τ : ⊤) →
               oneStepPair a (PairingLaw.faceExit law ω τ)
                           (PairingLaw.vExit law ω τ) ≡ T₀
oneStep-zero law a ω τ =
  oneStepPair-zero a (PairingLaw.faceExit law ω τ)
                    (PairingLaw.vExit law ω τ)
                    (PairingLaw.exit-opp law ω τ)

--------------------------------------------------------------------------------
-- §4. 里程碑 3 完成度
--
--   ✅ 构造性反例：C3 + coeffEx，twoStepCoeff = T₁ ≠ T₀（ex-sqzero-fails）
--   ✅ 裁决：路径 (b)——显式前提 PairingLaw（非 postulate，非造公理硬凑）
--   ✅ 带前提消元引理：oneStepPair-zero（⊗-zero 定义性 + cong 前提搬运）
--   ✅ PairingLaw 挂接：oneStep-zero（单胞腔版 ∂² 消元定理）
--   ⚠ 完整 ∂²=0：多胞腔 ⊕ 求和 + 枚举完备性 → 里程碑 4-5
--      （oneStep-zero 是 sum⊕ 折叠的基本步，pair-popping 直接适用）
--------------------------------------------------------------------------------
