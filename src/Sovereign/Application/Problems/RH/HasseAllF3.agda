{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.HasseAllF3
-- Hasse 界的 F₃ 全称形式（M1 · A1.5）—— RH 线第一个不带实例限定词的 ∀ 定理
--
-- 数学背景:
--   Hasse 界（q = 3）: 对非奇异 E/F₃，迹 t = q + 1 − #E 满足 t² ≤ 4q = 12，
--   即 t ∈ {−3,−2,−1,0,1,2,3}（ℤ），等价于 #E ∈ {1,…,7}（ℕ）。
--   本模块取 ℕ 形陈述——免去 Data.Integer.Properties 的序证明负担
--   （t = 4 − #E 的双向换算是算术事实；ℤ 迹见 CountF3.tℤ）。
--
-- 陈述:
--   HasseForm c  :=  (1 ≤ pointsE c) × (pointsE c ≤ 7)
--   hasse-all    :  ∀ (c : CurveF3) → IsNonSing c → HasseForm c
--
--   ∀ 对 record 类型 CurveF3 的全体元素分派（27 个构造子模式）:
--   · 9 条奇异分支: IsNonSing 假设归约后为「T₀ ≡ T₀ → ⊥」，h refl : ⊥，
--     ⊥-elim 吸收——奇异性假设在此真正被**使用**，不是装饰；
--   · 18 条非奇异分支: pointsE 归约为具体数字（A1.4 冻结表），≤ 链收口。
--
-- 诚实边界: 单看 ℕ 不等式，计数器对奇异曲线也落在 [1,7]（nsolY ≤ 2 的平凡推论）；
--   本定理的**内容**在「非奇异 ⇒ 该计数确为椭圆曲线的 F₃ 点数」这一解读下成立——
--   奇异曲线不是椭圆曲线，Hasse 对其不适用，故假设不可去。此解读属文档层，
--   形式内容即上述 ∀ 命题（对应计划文档 A1.5，验收门：陈述无实例限定词 ✓）。

module Sovereign.Application.Problems.RH.HasseAllF3 where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Application.Problems.RH.CurveF3
open import Sovereign.Application.Problems.RH.CountF3

--------------------------------------------------------------------------------
-- Hasse 形与全称定理
--------------------------------------------------------------------------------

HasseForm : CurveF3 → Set
HasseForm c = (1 ≤ pointsE c) × (pointsE c ≤ 7)

-- **∀①（A1.5）**: F₃ 上一切非奇异 Weierstrass 曲线满足 Hasse 界。
hasse-all : ∀ (c : CurveF3) → IsNonSing c → HasseForm c
hasse-all (mkC T₀ T₀ T₀) h = ⊥-elim (h refl)
hasse-all (mkC T₀ T₀ T₁) h = ⊥-elim (h refl)
hasse-all (mkC T₀ T₀ T₂) h = ⊥-elim (h refl)
hasse-all (mkC T₀ T₁ T₀) h = ( s≤s z≤n , s≤s (s≤s (s≤s (s≤s z≤n))) )        -- #E = 4
hasse-all (mkC T₀ T₁ T₁) h = ( s≤s z≤n , s≤s (s≤s (s≤s (s≤s z≤n))) )        -- #E = 4
hasse-all (mkC T₀ T₁ T₂) h = ( s≤s z≤n , s≤s (s≤s (s≤s (s≤s z≤n))) )        -- #E = 4
hasse-all (mkC T₀ T₂ T₀) h = ( s≤s z≤n , s≤s (s≤s (s≤s (s≤s z≤n))) )        -- #E = 4
hasse-all (mkC T₀ T₂ T₁) h = ( s≤s z≤n , s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) )  -- #E = 7
hasse-all (mkC T₀ T₂ T₂) h = ( s≤s z≤n , s≤s z≤n )                          -- #E = 1
hasse-all (mkC T₁ T₀ T₀) h = ⊥-elim (h refl)
hasse-all (mkC T₁ T₀ T₁) h = ( s≤s z≤n , s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) )        -- #E = 6
hasse-all (mkC T₁ T₀ T₂) h = ( s≤s z≤n , s≤s (s≤s (s≤s z≤n)) )                      -- #E = 3
hasse-all (mkC T₁ T₁ T₀) h = ⊥-elim (h refl)
hasse-all (mkC T₁ T₁ T₁) h = ( s≤s z≤n , s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) )        -- #E = 6
hasse-all (mkC T₁ T₁ T₂) h = ( s≤s z≤n , s≤s (s≤s (s≤s z≤n)) )                      -- #E = 3
hasse-all (mkC T₁ T₂ T₀) h = ( s≤s z≤n , s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) )        -- #E = 6
hasse-all (mkC T₁ T₂ T₁) h = ( s≤s z≤n , s≤s (s≤s (s≤s z≤n)) )                      -- #E = 3
hasse-all (mkC T₁ T₂ T₂) h = ⊥-elim (h refl)
hasse-all (mkC T₂ T₀ T₀) h = ⊥-elim (h refl)
hasse-all (mkC T₂ T₀ T₁) h = ( s≤s z≤n , s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))) )  -- #E = 5
hasse-all (mkC T₂ T₀ T₂) h = ( s≤s z≤n , s≤s (s≤s z≤n) )                    -- #E = 2
hasse-all (mkC T₂ T₁ T₀) h = ⊥-elim (h refl)
hasse-all (mkC T₂ T₁ T₁) h = ( s≤s z≤n , s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))) )  -- #E = 5
hasse-all (mkC T₂ T₁ T₂) h = ( s≤s z≤n , s≤s (s≤s z≤n) )                    -- #E = 2
hasse-all (mkC T₂ T₂ T₀) h = ( s≤s z≤n , s≤s (s≤s z≤n) )                    -- #E = 2
hasse-all (mkC T₂ T₂ T₁) h = ⊥-elim (h refl)
hasse-all (mkC T₂ T₂ T₂) h = ( s≤s z≤n , s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))) )  -- #E = 5
