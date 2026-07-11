{-# OPTIONS --guardedness #-}

-- | Sovereign.Base.Trit
-- 律算基础：GF(3) 三进制定义与运算
--
-- 核心公理：宇宙最小几何单元为 GF(3) 格点。
-- 包含：Trit {0, 1, 2}，加法和乘法运算。

module Sovereign.Base.Trit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- 1. Trit 数据类型 (GF(3))
--------------------------------------------------------------------------------

-- 驻波三态：吸收态 (0), 平衡态 (1), 表达态 (2)
data Trit : Set where
  T₀ : Trit  -- 0
  T₁ : Trit  -- 1
  T₂ : Trit  -- 2

-- Trit 到自然数 ℕ（本源表示）
tritToℕ : Trit → ℕ
tritToℕ T₀ = 0
tritToℕ T₁ = 1
tritToℕ T₂ = 2

-- Trit 到编码值 {0, 1, 2} (用于工程打包，恒等映射)
tritToCode : Trit → ℕ
tritToCode T₀ = 0
tritToCode T₁ = 1
tritToCode T₂ = 2

-- 编码值到 Trit
codeToTrit : ℕ → Trit
codeToTrit 0 = T₀
codeToTrit 1 = T₁
codeToTrit 2 = T₂
codeToTrit _ = T₀ -- 默认归零

--------------------------------------------------------------------------------
-- 3. GF(3) 运算
--------------------------------------------------------------------------------

-- 加法 (模 3)
-- 对应律算中的"损益"微调或相位叠加
_⊕_ : Trit → Trit → Trit
T₀ ⊕ y = y
T₁ ⊕ T₀ = T₁
T₁ ⊕ T₁ = T₂
T₁ ⊕ T₂ = T₀
T₂ ⊕ T₀ = T₂
T₂ ⊕ T₁ = T₀
T₂ ⊕ T₂ = T₁

-- 乘法 (模 3)
_⊗_ : Trit → Trit → Trit
T₀ ⊗ _ = T₀
_ ⊗ T₀ = T₀
T₁ ⊗ x = x
T₂ ⊗ T₂ = T₁
_ ⊗ _ = T₁

--------------------------------------------------------------------------------
-- 4. 核心验证
--------------------------------------------------------------------------------

-- 归零公理验证：T₁ + T₂ = T₀ (1 + 2 = 3 ≡ 0)
verifyZero : T₁ ⊕ T₂ ≡ T₀
verifyZero = refl

-- 乘法验证：T₂ ⊗ T₂ = T₁ (2 × 2 = 4 ≡ 1)
verifyMul : T₂ ⊗ T₂ ≡ T₁
verifyMul = refl
