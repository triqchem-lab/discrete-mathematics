{-# OPTIONS --rewriting #-}

-- | Sovereign.Structology.WuXingEulerHFM
-- 柏拉图立体 Euler 示性数的 HFM 交叉验证
--   χ = V - E + F = 2 (全部 5 种立体, 球面拓扑)
--
-- HFM 验证: test/ExtendedVerify.hs
--
-- 数学原理 (Euler 多面体定理):
--   对于球面同胚的多面体, 顶点数 V、棱数 E、面数 F 满足:
--     V - E + F = 2
--   这是 Euler 示性数 χ(S²) = 2 的组合学表达
--   拓扑意义: 球面的 Euler 示性数为 2, 与三角剖分无关
--
-- 五种柏拉图立体与五行对称群的对应:
--   火 Fire    — 正四面体 (Tetrahedron)     → A₄  (12 阶)
--   土 Earth   — 正六面体 (Cube)            → O_h (48 阶)
--   金 Metal   — 正十二面体 (Dodecahedron)  → I_h (120 阶)
--   水 Water   — 正二十面体 (Icosahedron)   → I   (60 阶)
--   木 Wood    — 正八面体 (Octahedron)      → O   (24 阶)
--
-- 群阶公式 (WuXingTransition.agda):
--   正四面体: 4 面 × 3 边           = 12 = |A₄|
--   正六面体: 6 面 × 4 边 × 2      = 48 = |O_h|
--   正八面体: 8 面 × 3 边           = 24 = |O|
--   正十二面体: 12 面 × 5 边 × 2   = 120 = |I_h|
--   正二十面体: 20 面 × 3 边        = 60 = |I|

module Sovereign.Structology.WuXingEulerHFM where

open import Data.Integer using (ℤ; +_; _+_; _-_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 正四面体 (火 Fire → A₄)
-- V=4, E=6, F=4
-- χ = V-E+F = 4-6+4 = 2
tetV : ℤ; tetV = + 4
tetE : ℤ; tetE = + 6
tetF : ℤ; tetF = + 4
tetChi : ℤ; tetChi = tetV - tetE + tetF
tetChi-ok : tetChi ≡ + 2; tetChi-ok = refl

-- 正六面体 (土 Earth → O_h)
-- V=8, E=12, F=6
cubeV : ℤ; cubeV = + 8
cubeE : ℤ; cubeE = + 12
cubeF : ℤ; cubeF = + 6
cubeChi : ℤ; cubeChi = cubeV - cubeE + cubeF
cubeChi-ok : cubeChi ≡ + 2; cubeChi-ok = refl

-- 正八面体 (木 Wood → O)
-- V=6, E=12, F=8
octV : ℤ; octV = + 6
octE : ℤ; octE = + 12
octF : ℤ; octF = + 8
octChi : ℤ; octChi = octV - octE + octF
octChi-ok : octChi ≡ + 2; octChi-ok = refl

-- 正十二面体 (金 Metal → I_h)
-- V=20, E=30, F=12
dodV : ℤ; dodV = + 20
dodE : ℤ; dodE = + 30
dodF : ℤ; dodF = + 12
dodChi : ℤ; dodChi = dodV - dodE + dodF
dodChi-ok : dodChi ≡ + 2; dodChi-ok = refl

-- 正二十面体 (水 Water → I)
-- V=12, E=30, F=20
icoV : ℤ; icoV = + 12
icoE : ℤ; icoE = + 30
icoF : ℤ; icoF = + 20
icoChi : ℤ; icoChi = icoV - icoE + icoF
icoChi-ok : icoChi ≡ + 2; icoChi-ok = refl

-- 五种立体全部满足 χ=2, 说明它们都是球面同胚
-- Duality: 立方体 ↔ 八面体, 十二面体 ↔ 二十面体, 四面体自对偶
-- 对偶立体的 V 与 F 互换, E 不变, χ 不变
