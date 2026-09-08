{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Character.FrequencyMode
-- 频率模态接口 — DC 特征谱作为波/振动频率的公共地基 (2026-09-08)
--
-- 背景: 量子叠加/纠缠/驻波/声子/谐波/泛音等"波/振动频率衔接"概念在代码库
-- 散落多层 (A₄/GF3/ℕ×144/ℚ), 未统一. 而 DCCharacter 已在 DC 本源上完备形式化
-- DC 的 12 特征谱 (χ = ζ₃^振幅频 · ζ₄^相位频, 正交/Parseval/反射全证), 但孤立无下游.
--
-- 本模块把 DC 特征谱提炼为"频率模态"接口, 作为频率类模块的公共地基:
--   频率模态 = CharacterIndex = (振幅频 u ∈ F₃) × (相位频 v ∈ C₄)  = 12 模态
--   模态 → DC 特征 χ (复用 DCCharacter.dc-character, 0 postulate)
--   12 模态 = DC 的完整振动谱 (幅度 3 频 × 相位 4 频 = 12)
--
-- 复用: DCCharacter (DC 特征谱, 3707 行, 0 postulate)
-- 0 postulate.

module Sovereign.Algebra.Character.FrequencyMode where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Fin using (toℕ)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GroupTheory.DuodecClock
  using (AlphaPower; a0; a1; a2; a3; DuodecPoint; mixedOp)
open import Sovereign.Algebra.Character.DCCharacter
  using (CharacterIndex; Z12Sys; _*ᶻ_; conjᶻ; z0; sum-over-DC;
         dc-character; dc-character-hom; orthogonality; charIndexToNat)

--------------------------------------------------------------------------------
-- §1. 频率模态 = DC 特征索引 (振幅频 × 相位频)
--------------------------------------------------------------------------------

-- 频率模态: (u, v) = 振幅频率 u ∈ F₃ × 相位频率 v ∈ C₄
-- 物理: 波的振动模态 = 幅度振动频 × 相位旋转频
FrequencyMode : Set
FrequencyMode = CharacterIndex

-- 模态数 = 3 × 4 = 12 (与 DC 元素数一致, 对偶群)
mode-count : ℕ
mode-count = 12

-- 12 模态 = DC 的完整振动谱: 每个模态是一个 DC 特征 χ₍u,v₎
-- 模态 → 特征值 (在 DuodecPoint 上, 复用 DCCharacter)

-- 模态的振幅频率分量
mode-amp : FrequencyMode → Trit
mode-amp = proj₁

-- 模态的相位频率分量
mode-phase : FrequencyMode → AlphaPower
mode-phase = proj₂

-- 模态编号 (0..11): (u,v) ↦ u·4 + v
mode-index : FrequencyMode → ℕ
mode-index = charIndexToNat

--------------------------------------------------------------------------------
-- §2. 模态 → DC 特征 (频率衔接的展示群实现)
--------------------------------------------------------------------------------

-- 模态 (u,v) 的 DC 特征: χ₍u,v₎(p) = ζ₃^(u·t) · ζ₄^(v∘k)
-- 即: 该频率模态在 DC 元素 p 上的振动值
mode-character : FrequencyMode → DuodecPoint → Z12Sys
mode-character = dc-character

-- 特征是群同态 (频率衔接: 模态在 mixedOp 上可乘 — 振动叠加)
mode-character-hom : ∀ (m : FrequencyMode) (p q : DuodecPoint) →
  mode-character m (mixedOp p q) ≡ mode-character m p *ᶻ mode-character m q
mode-character-hom = dc-character-hom

--------------------------------------------------------------------------------
-- §3. 模态正交 (波的衔接: 不同频率模态不干扰)
--------------------------------------------------------------------------------

-- 不同模态 (u,v) ≠ (u',v') 的特征正交: 内积 = 0
-- 物理: 不同频率的波互不干扰, 可独立叠加 (傅里叶衔接)
mode-orthogonal : ∀ u v u' v' →
  (u ≢ u') ⊎ (v ≢ v') →
  sum-over-DC (λ x → dc-character (u , v) x *ᶻ conjᶻ (dc-character (u' , v') x)) ≡ z0
mode-orthogonal = orthogonality

-- 自内积 (同模态): Σ |χ|² = 12 (模态能量)
-- (由 DCCharacter 的 §5′ 自内积提供, 此处转发接口)

--------------------------------------------------------------------------------
-- §4. 显式 12 频率模态 (振幅频 u ∈ {T₀,T₁,T₂} × 相位频 v ∈ {a0,a1,a2,a3})
--------------------------------------------------------------------------------

-- 基频模态: (T₀, a0) — 振幅静止 × 相位静止 (0 频)
mode-00 : FrequencyMode ; mode-00 = (T₀ , a0)
-- 振幅 1 频 × 相位静止
mode-10 : FrequencyMode ; mode-10 = (T₁ , a0)
mode-20 : FrequencyMode ; mode-20 = (T₂ , a0)
-- 相位 90° 频 (×a1) × 振幅静止
mode-01 : FrequencyMode ; mode-01 = (T₀ , a1)
mode-11 : FrequencyMode ; mode-11 = (T₁ , a1)
mode-21 : FrequencyMode ; mode-21 = (T₂ , a1)
-- 相位 180° 频 (×a2)
mode-02 : FrequencyMode ; mode-02 = (T₀ , a2)
mode-12 : FrequencyMode ; mode-12 = (T₁ , a2)
mode-22 : FrequencyMode ; mode-22 = (T₂ , a2)
-- 相位 270° 频 (×a3)
mode-03 : FrequencyMode ; mode-03 = (T₀ , a3)
mode-13 : FrequencyMode ; mode-13 = (T₁ , a3)
mode-23 : FrequencyMode ; mode-23 = (T₂ , a3)
