{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.VectorDirection
-- 矢量方向计数: 卢先生「幻方」的矢量义 (0 postulate)
--
-- 术语边界 (docs/cross-level/magic-square-terminology.md):
--   卢先生「幻方」的阶数 n = 同时在变的矢量方向(变量)个数, 与「行列对角线和」无关。
--   本模块把这一矢量义形式化:  n 阶幻方 = n 个矢量方向 = Vec Trit n (Tⁿ 环面的 n 维)。
--
-- 对齐离散全息框架:
--   一个矢量方向 = 一个 GF(3) 自由度 (Trit)
--   n 个矢量方向 = Vec Trit n  (GF(3)ⁿ, 共 3ⁿ 个格点)
--   T⁶ 环面 = 6 个矢量方向 = Vec (Fin 3) 6  (Trit ≅ Fin 3)
--   4 阶  = 3 空间 + 1 时间 = 4 个矢量方向
--   144 阶 = 12 维对称关系 = 12 × 12 = 144 个矢量方向/力学关系
--   排列数 n! = 置换群 Sₙ 的大小 (144! ≈ 1.51×10⁹⁶, 组合爆炸非浮点精度)

module Sovereign.Structology.VectorDirection where

open import Data.Nat using (ℕ; zero; suc; _*_; _^_; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

--------------------------------------------------------------------------------
-- §1. 一个矢量方向 = 一个 GF(3) 自由度
--------------------------------------------------------------------------------

Direction : Set
Direction = Trit

--------------------------------------------------------------------------------
-- §2. n 阶「幻方」(卢先生矢量义) = n 个矢量方向
--------------------------------------------------------------------------------

-- 类型: n 个矢量方向 (n 个自由度)
MagicSquareᵛ : ℕ → Set
MagicSquareᵛ n = Vec Direction n

-- 阶数 = 矢量方向个数 (恒等于 n)
order : {n : ℕ} → MagicSquareᵛ n → ℕ
order {n} _ = n

-- Trit ≅ Fin 3 (与 T⁶ = Vec (Fin 3) 6 对齐)
tritToFin : Trit → Fin 3
tritToFin T₀ = zero
tritToFin T₁ = suc zero
tritToFin T₂ = suc (suc zero)

--------------------------------------------------------------------------------
-- §3. 具体锚点
--------------------------------------------------------------------------------

-- 4 阶 = 3 空间 + 1 时间 (4 个矢量方向)
fourDirections : MagicSquareᵛ 4
fourDirections = T₀ ∷ T₁ ∷ T₂ ∷ T₀ ∷ []

-- 6 阶 = T⁶ 环面 (6 个矢量方向)
sixDirections : MagicSquareᵛ 6
sixDirections = T₀ ∷ T₁ ∷ T₂ ∷ T₀ ∷ T₁ ∷ T₂ ∷ []

-- 阶数 = 方向个数 (refl)
order-four : order fourDirections ≡ 4
order-four = refl

order-six : order sixDirections ≡ 6
order-six = refl

-- 144 阶 = 12 维对称关系 = 12 × 12
twelve-squared : 12 * 12 ≡ 144
twelve-squared = refl

-- n 个矢量方向的空间有 3ⁿ 个格点; T⁶: 3⁶ = 729
t6-points : 3 ^ 6 ≡ 729
t6-points = refl

--------------------------------------------------------------------------------
-- §4. 排列数 n! = 置换群 Sₙ 的大小 (组合爆炸, 非浮点精度)
--------------------------------------------------------------------------------

fact : ℕ → ℕ
fact zero = 1
fact (suc n) = suc n * fact n

-- double 精确整数边界: 18! < 2⁵³ < 19!
fact18 : fact 18 ≡ 6402373705728000
fact18 = refl

fact19 : fact 19 ≡ 121645100408832000
fact19 = refl

-- 0 postulate.
