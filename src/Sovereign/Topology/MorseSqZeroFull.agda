{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseSqZeroFull
-- M3 里程碑 4-5：多胞腔 pair-popping——带 PairingLaw 前提的完整 ∂²=0
--
-- 证明结构（复用最大化）：
--   MorsePairingLaw.oneStepPair-zero —— 单胞腔消元（出口互补 ⟹ 项 = T₀）
--   ⊕ 第一子句 T₀ ⊕ s ≡ s —— 头跳定义性
--   列表归纳 —— 全列表消元
--
-- 定理：对满足 PairingLaw（出口互补律）的任意胞腔列表 ωs，
--       带出口两步系数和 sumFull σ τ ωs ≡ T₀。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseSqZeroFull where

open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Data.Empty using (⊥)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Topology.MorsePartialG
open import Sovereign.Topology.MorsePairingLaw
  using (PairingLaw; oneStepPair; oneStepPair-zero; C3; cσ; cω; cτ)

--------------------------------------------------------------------------------
-- §1. 带出口两步系数——逐 ω 嵌入 PairingLaw
--
--   twoStepFull σ ω τ = a_ω ⊗ (b_ωτ ⊕ e'_ωτ)
--     a_ω  = coeff σ ω       （进入 ω 的系数——MorsePartialG）
--     b_ωτ = faceExit ω τ    （面出口——PairingLaw）
--     e'_ωτ = vExit ω τ      （V 出口——PairingLaw）
--------------------------------------------------------------------------------

module MultiStep (K : Set) (Face : K → K → Set) (V : K → Maybe K) where

  twoStepFull : MorsePartialG K Face V → PairingLaw K → K → K → K → Trit
  twoStepFull pg law σ ω τ =
    oneStepPair (MorsePartialG.coeff pg σ ω)
                (PairingLaw.faceExit law ω τ)
                (PairingLaw.vExit law ω τ)

  -- 列表求和（结构递归）
  sumFull : MorsePartialG K Face V → PairingLaw K → K → K → List K → Trit
  sumFull pg law σ τ []       = T₀
  sumFull pg law σ τ (ω ∷ ws) =
    twoStepFull pg law σ ω τ ⊕ sumFull pg law σ τ ws

  -- §2. 头跳引理：头项 ≡ T₀ ⟹ 和 = 尾和
  --     (T₀ ⊕ s) ≡ s 是 ⊕ 第一子句（定义性）
  head-skip : (pg : MorsePartialG K Face V) (law : PairingLaw K)
              (σ τ ω : K) (ws : List K) →
              twoStepFull pg law σ ω τ ≡ T₀ →
              sumFull pg law σ τ (ω ∷ ws) ≡ sumFull pg law σ τ ws
  head-skip pg law σ τ ω ws h = trans (cong (λ z → z ⊕ sumFull pg law σ τ ws) h) refl

  --------------------------------------------------------------------------------
  -- §3. 主定理 M3.4：完整 ∂² = 0（带 PairingLaw 前提）
  --
  --   逐 ω 应用 oneStepPair-zero（出口互补 ⟹ 项 = T₀），
  --   头跳归纳，全列表和 ≡ T₀。
  --------------------------------------------------------------------------------

  all-zero : (pg : MorsePartialG K Face V) (law : PairingLaw K)
             (σ τ : K) (ws : List K) →
             sumFull pg law σ τ ws ≡ T₀
  all-zero pg law σ τ []       = refl
  all-zero pg law σ τ (ω ∷ ws) =
    trans (head-skip pg law σ τ ω ws
             (oneStepPair-zero (MorsePartialG.coeff pg σ ω)
                               (PairingLaw.faceExit law ω τ)
                               (PairingLaw.vExit law ω τ)
                               (PairingLaw.exit-opp law ω τ)))
          (all-zero pg law σ τ ws)

--------------------------------------------------------------------------------
-- §4. 里程碑 6：实例交叉——平凡 PairingLaw + 具体列表数值验证
--
--   平凡律：faceExit = T₁，vExit = T₂，exit-opp = refl（T₁⊕T₂ = T₀ 定义性）
--   对任意 K 可构造——PairingLaw 非空性的见证。
--------------------------------------------------------------------------------

trivialLaw : (K : Set) → PairingLaw K
trivialLaw K = record
  { faceExit = λ _ _ → T₁
  ; vExit    = λ _ _ → T₂
  ; exit-opp = λ _ _ → refl
  }
-- T₁ ⊕ T₂ ≡ T₀ 定义性（⊕ 第三子句）——与 K₃ m3-cancel 同一形状

-- 实例：K = C3（复用反例的胞腔类型），2 胞腔列表数值验证
open MultiStep C3 (λ _ _ → ⊥) (λ _ → nothing)

lawC3 : PairingLaw C3
lawC3 = trivialLaw C3

-- coeff：全 T₂（任意数据——消元不依赖它）
coeffC3 : C3 → C3 → Trit
coeffC3 _ _ = T₂

pgC3 : MorsePartialG C3 (λ _ _ → ⊥) (λ _ → nothing)
pgC3 = record
  { isCritical = λ _ → ⊥
  ; coeff      = coeffC3
  ; routeList  = λ _ → []
  }

-- 数值 sanity：2 胞腔列表的 sumFull = T₂⊗(T₁⊕T₂) ⊕ T₂⊗(T₁⊕T₂) = T₀⊕T₀ = T₀
sanity-2 : sumFull pgC3 lawC3 cσ cτ (cω ∷ cσ ∷ []) ≡ T₀
sanity-2 = all-zero pgC3 lawC3 cσ cτ (cω ∷ cσ ∷ [])

-- 数值 sanity：空列表（base case 定义性）
sanity-0 : sumFull pgC3 lawC3 cσ cτ [] ≡ T₀
sanity-0 = refl

-- 单胞腔数值展开（透明化：T₂⊗(T₁⊕T₂) = T₂⊗T₀ = T₀）
sanity-1-expand : twoStepFull pgC3 lawC3 cσ cω cτ ≡ T₀
sanity-1-expand = refl

--------------------------------------------------------------------------------
-- §5. 里程碑 4-6 完成度
--
--   ✅ M3.4 主定理 all-zero：完整 ∂²=0（PairingLaw 前提下任意列表）
--   ✅ 证明结构：oneStepPair-zero（单胞腔）+ head-skip（头跳）+ 列表归纳
--   ✅ M3.6 实例交叉：trivialLaw（PairingLaw 非空见证）+ 3 个数值 sanity
--   ✅ 复用：MorsePairingLaw.oneStepPair-zero + ⊕ 头跳定义性 + K₃ m3-cancel 形状
--
--   对照风险闸：PairingLaw 是 record 前提（非 postulate），
--   反例（MorsePairingLaw.ex-sqzero-fails）证明此前提不可省——
--   泛型 ∂²=0 = 带显式前提的定理（诚实边界已登记）。
--
--   泛型与实例的对账：m3-cancel（K₃）= trivialLaw 的 exit-opp 形状；
--   m3-assembly（T₂⊗(T₁⊕T₂)≡T₀）= sanity-1-expand 的定义性展开。
--------------------------------------------------------------------------------
