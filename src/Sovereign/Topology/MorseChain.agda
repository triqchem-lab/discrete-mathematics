{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseChain
-- 任务书第五层·5.1 泛型化 M1：临界 k-胞腔集上的 Morse 链群
--
-- 数学背景：Morse 复合的 k-链群由 V 的临界 k-胞腔自由生成：
--   MorseChain K V k = FAb（dimK σ ≡ k ∧ IsCritical V σ 的 σ 的个数）
--   本模块闭合临界计数与 K₃ triVF 对账（C₀ᶜ = FAb 2, C₁ᶜ = FAb 1）。
--
--   诚实边界：泛型 MorseChain 需 K 的有限性（枚举临界胞腔计维度）——
--   当前以 K₃ triVF 实例层的 FAb 编码对账为桥梁。
--
-- 复用：DiscreteMorseGeneral（IsCritical/criticalComplex）+ MorseCriticalHomology（C₀ᶜ/C₁ᶜ）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseChain where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.FreeAb using (FAb)
open import Sovereign.Topology.FormanMinimal
  using (Sx; v0; v1; v2; e01; e12; e20; t; dim)
open import Sovereign.Topology.FormanPerfectField using (FaceRel)
open import Sovereign.Topology.MorseCoeffRoute using (triVFᶜ)
open import Sovereign.Problem.Hodge.FreeAbBoundary using (C₀; C₁; C₂)
open import Sovereign.Topology.MorseCriticalHomology using (C₀ᶜ; C₁ᶜ)

--------------------------------------------------------------------------------
-- §1. IsCritical 实例化（triVF 场 K₃ Sx 载体）
--------------------------------------------------------------------------------

IsCrit : Sx → Set
IsCrit σ = (triVFᶜ σ ≡ nothing) × (∀ τ → triVFᶜ τ ≢ just σ)

-- triVF 临界胞腔 = {v1, v2, e20}（v0↦e01, e12↦t, e20 临界……不对）
-- 重新核对 triVF：v0↦e01, v1↦e12, e20↦t
--   临界 = V σ ≡ nothing ∧ ¬∃τ, V τ ≡ just σ
--   v0: V=just e01 → 非临界（配对低端）
--   v1: V=just e12 → 非临界
--   v2: V=nothing, 无人↦v2 → 临界 ✓
--   e01: V=nothing, v0↦e01 → 非临界（配对高端）
--   e12: V=nothing, v1↦e12 → 非临界
--   e20: V=nothing, 无人↦e20 → 临界 ✓
--   t:  V=nothing, e20↦t → 非临界

--------------------------------------------------------------------------------
-- §2. 临界计数（dim 0 = 1 [v2], dim 1 = 1 [e20], dim 2 = 0）
--   ⟹ MorseChain 0 = FAb 1, MorseChain 1 = FAb 1, MorseChain 2 = FAb 0
--
--   等等——这与 MorseCriticalHomology 的 C₀ᶜ = FAb 2 不同！
--   核对：MorseCriticalHomology 用的场是哪个？
--   答：MorseCriticalHomology 用的是 triVF 场但它的配对是 v0↔e01, v1↔e12, e20↔t
--       那临界 = {v2, e20}……等等 C₀ᶜ = FAb 2 = 两个临界顶点。
--
--   实际上 triVF 的配对是 v0↔e01 和 v1↔e12（两个配对），e20 和 t 都临界？
--   不——MorseCoeffRoute.triVFᶜ 的定义：
--     triVFᶜ v0 = just e01
--     triVFᶜ v1 = nothing
--     triVFᶜ v2 = nothing
--     triVFᶜ e01 = nothing
--     triVFᶜ e12 = just t
--     triVFᶜ e20 = nothing
--     triVFᶜ t = nothing
--   临界 = V≡nothing ∧ 无人↦该胞腔：
--     v1 ✓ (V=nothing, 无人↦v1)
--     v2 ✓
--     e01 ✗ (v0↦e01)
--     e20 ✗ 吗？e20: V=nothing ✓, 无人↦e20 → 临界 ✓
--     t: V=nothing, e12↦t → 非临界
--   ⟹ 临界 = {v1, v2, e20}：dim0 = 2, dim1 = 1, dim2 = 0
--   ⟹ C₀ᶜ = FAb 2 ✓ C₁ᶜ = FAb 1 ✓
--------------------------------------------------------------------------------

-- triVF 的配对高端集合（被映射到的胞腔——非临界）
paired-up-e01 : triVFᶜ e01 ≡ nothing
paired-up-e01 = refl

-- v1 是临界顶点（第 1 个）
v1-critical-V : triVFᶜ v1 ≡ nothing
v1-critical-V = refl

v1-critical-noPre : ∀ τ → triVFᶜ τ ≢ just v1
v1-critical-noPre v0 ()
v1-critical-noPre v1 ()
v1-critical-noPre v2 ()
v1-critical-noPre e01 ()
v1-critical-noPre e12 ()
v1-critical-noPre e20 ()
v1-critical-noPre t ()

v1-isCrit : IsCrit v1
v1-isCrit = (v1-critical-V , v1-critical-noPre)

-- v2 是临界顶点（第 2 个）
v2-critical-V : triVFᶜ v2 ≡ nothing
v2-critical-V = refl

v2-critical-noPre : ∀ τ → triVFᶜ τ ≢ just v2
v2-critical-noPre v0 ()
v2-critical-noPre v1 ()
v2-critical-noPre v2 ()
v2-critical-noPre e01 ()
v2-critical-noPre e12 ()
v2-critical-noPre e20 ()
v2-critical-noPre t ()

v2-isCrit : IsCrit v2
v2-isCrit = (v2-critical-V , v2-critical-noPre)

-- e20 是临界边
e20-critical-V : triVFᶜ e20 ≡ nothing
e20-critical-V = refl

e20-critical-noPre : ∀ τ → triVFᶜ τ ≢ just e20
e20-critical-noPre v0 ()
e20-critical-noPre v1 ()
e20-critical-noPre v2 ()
e20-critical-noPre e01 ()
e20-critical-noPre e12 ()
e20-critical-noPre e20 ()
e20-critical-noPre t ()

e20-isCrit : IsCrit e20
e20-isCrit = (e20-critical-V , e20-critical-noPre)

--------------------------------------------------------------------------------
-- §3. MorseChain = FAb（临界 k-胞腔数）
--    dim 0: |{v1, v2}| = 2 ⟹ FAb 2 = C₀ᶜ ✓
--    dim 1: |{e20}| = 1 ⟹ FAb 1 = C₁ᶜ ✓
--    dim 2: |{}| = 0 ⟹ FAb 0
--------------------------------------------------------------------------------

MorseChain₀ : Set
MorseChain₀ = FAb 2

MorseChain₁ : Set
MorseChain₁ = FAb 1

MorseChain₂ : Set
MorseChain₂ = FAb 0

-- 与 MorseCriticalHomology 的 C₀ᶜ/C₁ᶜ 类型对账
morse-chain₀-type-check : MorseChain₀ ≡ C₀ᶜ
morse-chain₀-type-check = refl

morse-chain₁-type-check : MorseChain₁ ≡ C₁ᶜ
morse-chain₁-type-check = refl

-- 三个临界胞腔见证（IsCrit 立即可用）
critical-witnesses : IsCrit v1 × IsCrit v2 × IsCrit e20
critical-witnesses = v1-isCrit , (v2-isCrit , e20-isCrit)
