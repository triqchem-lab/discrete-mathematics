{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.StandingWave
-- 三代 = 三个驻波构型 (波节 T₀ / 波峰 T₁ / 波谷 T₂), 0 postulate
--
-- 本体: 三代费米子不是三个独立粒子, 而是同一手征旋转 (CW/CCW 共轭) 的
--   三个稳定驻波构型。A₄ 三维表示在 Z₃ 子群上分支 3 = 1 ⊕ 1′ ⊕ 1″,
--   三个一维特征标恰好是三个驻波构型 (波节/波峰/波谷)。
--
-- 干涉规则 (GF(3) 加法 ⊕):
--   同相     T₁ ⊕ T₁ = T₂   (波峰 + 波峰 → 波谷)
--   反相     T₁ ⊕ T₂ = T₀   (波峰 + 波谷 → 波节)
--   同相偏移 T₂ ⊕ T₂ = T₁   (波谷 + 波谷 → 波峰)
--
-- 三代循环 (⊕ T₁ 即 C₃ 生成元): T₀ → T₁ → T₂ → T₀ (生之序)

module Sovereign.Structology.StandingWave where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Structology.A4Representation using (Zω; oneZω; ω; ω²)

--------------------------------------------------------------------------------
-- §1. 驻波构型 = GF(3) 三态
--------------------------------------------------------------------------------

WaveMode : Set
WaveMode = Trit

-- 三态命名 (三代)
node   : WaveMode   -- 波节 (第一代, 吸收态 T₀)
node   = T₀
peak   : WaveMode   -- 波峰 (第二代, 平衡态 T₁)
peak   = T₁
trough : WaveMode   -- 波谷 (第三代, 干涉态 T₂)
trough = T₂

-- 干涉 = GF(3) 加法 ⊕ (两旋向在同一点的叠加)
interfere : WaveMode → WaveMode → WaveMode
interfere = _⊕_

--------------------------------------------------------------------------------
-- §2. 驻波形成三律 (干涉表, refl)
--------------------------------------------------------------------------------

law-peak   : interfere T₁ T₁ ≡ T₂   -- 同相 → 波谷
law-peak   = refl
law-node   : interfere T₁ T₂ ≡ T₀   -- 反相 → 波节
law-node   = refl
law-trough : interfere T₂ T₂ ≡ T₁   -- 同相偏移 → 波峰
law-trough = refl

--------------------------------------------------------------------------------
-- §3. 三代循环 (⊕ T₁ 即 C₃ 生成元, 生之序 T₀→T₁→T₂→T₀)
--------------------------------------------------------------------------------

gen-cycle : (interfere T₀ T₁ ≡ T₁) × (interfere T₁ T₁ ≡ T₂) × (interfere T₂ T₁ ≡ T₀)
gen-cycle = refl , refl , refl

--------------------------------------------------------------------------------
-- §4. 三代 ↔ 三个一维特征标 (Z₃ 分支 3 = 1 ⊕ 1′ ⊕ 1″)
--   generation m = 对应一维特征标在 3 循环上的区分值
--------------------------------------------------------------------------------

generation : WaveMode → Zω
generation T₀ = oneZω   -- 第一代 = χ₁  (平凡特征)
generation T₁ = ω       -- 第二代 = χ₁′ (ω 特征)
generation T₂ = ω²      -- 第三代 = χ₁″ (ω² 特征)

-- 0 postulate.
