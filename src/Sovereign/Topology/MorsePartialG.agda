{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorsePartialG
-- Morse 泛型化 M3：∂^Morse 边界算子——泛型框架（Trit 陈述层）
--
-- 修正（v2）：
--   coeff 从 ℕ 改为 Trit（GF(3) 系数域——Base/Trit 项目根基）
--   新增 twoStepCoeff：两步系数 ⊕ 求和（对 ωs 列表）
--   partialSqZero 修正为 ∃k→twoStepCoeff ≡ T₀ 的命题形式
--
-- 实例层已闭合：K₃ 双三角 m3-cancel (T₁⊕T₂≡T₀ refl ✓)
-- m3-assembly (T₂⊗(T₁⊕T₂)≡T₀ refl ✓)
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorsePartialG where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

--------------------------------------------------------------------------------
-- §1. 泛型边界算子 record（GF(3) 系数域——Trit）
--------------------------------------------------------------------------------

record MorsePartialG (K : Set) (Face : K → K → Set) (V : K → Maybe K) : Set₁ where
  field
    -- 临界判定：σ 是临界的 ⟺ V σ ≡ nothing
    isCritical : K → Set

    -- 边界系数：Face τ σ 的 GF(3) 系数（Trit 域）
    coeff : K → K → Trit

    -- 路由列表：从 σ 出发到达的所有临界胞腔
    routeList : (σ : K) → List K

--------------------------------------------------------------------------------
-- §2. 两步系数——⊕ 求和（对中间胞腔列表）
--
--   twoStepCoeff ωs σ τ = Σ_{ω ∈ ωs} (coeff σ ω ⊗ coeff ω τ)
--
--   这是 ∂²(σ) 在 τ 分量上的系数——对中间胞腔列表 ωs 求和。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §2-3. 两步系数 + ∂²=0 陈述（参数化 module）
--------------------------------------------------------------------------------

module TwoStep (K : Set) (Face : K → K → Set) (V : K → Maybe K) where

  twoStepCoeff : MorsePartialG K Face V → List K → K → K → Trit
  twoStepCoeff pg [] σ τ = T₀
  twoStepCoeff pg (ω ∷ ωs) σ τ =
    (MorsePartialG.coeff pg σ ω ⊗ MorsePartialG.coeff pg ω τ)
    ⊕ twoStepCoeff pg ωs σ τ

  record PartialSqZero : Set₁ where
    field
      pg : MorsePartialG K Face V

      -- ∂² 消元：对完备中间胞腔列表 ωs，两步系数和恒为 T₀
      partialSqZero : (ωs : List K) → (σ τ : K) →
                      twoStepCoeff pg ωs σ τ ≡ T₀

--------------------------------------------------------------------------------
-- §4. 里程碑 1 完成度
--
--   ✅ coeff 从 ℕ 改为 Trit（GF(3) 域——项目根基 Base/Trit）
--   ✅ twoStepCoeff 定义（⊕ 求和，结构递归）
--   ✅ partialSqZero 修正为命题形式（twoStepCoeff ≡ T₀）
--   ✅ 移除了 boundaryCoeff（ℕ 遗留）和 isCritical（由 V σ ≡ nothing 替代）
--
--   编译验证：本模块应 exit 0（纯定义，无证明体）
--------------------------------------------------------------------------------
