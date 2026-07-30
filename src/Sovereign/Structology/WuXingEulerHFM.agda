{-# OPTIONS --rewriting #-}

-- | Sovereign.Structology.WuXingEulerHFM
-- 柏拉图立体 Euler 示性数的 HFM 交叉验证
--   χ = V - E + F = 2 (全部 5 种立体, 球面拓扑)
-- HFM verified: test/ExtendedVerify.hs

module Sovereign.Structology.WuXingEulerHFM where

open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; +_; _+_; _-_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Tetrahedron (火) → A₄
tetV : ℤ; tetV = + 4
tetE : ℤ; tetE = + 6
tetF : ℤ; tetF = + 4
tetChi : ℤ; tetChi = tetV - tetE + tetF
tetChi-ok : tetChi ≡ + 2; tetChi-ok = refl

-- Cube (土) → O_h
cubeV : ℤ; cubeV = + 8
cubeE : ℤ; cubeE = + 12
cubeF : ℤ; cubeF = + 6
cubeChi : ℤ; cubeChi = cubeV - cubeE + cubeF
cubeChi-ok : cubeChi ≡ + 2; cubeChi-ok = refl

-- Octahedron (木) → O
octV : ℤ; octV = + 6
octE : ℤ; octE = + 12
octF : ℤ; octF = + 8
octChi : ℤ; octChi = octV - octE + octF
octChi-ok : octChi ≡ + 2; octChi-ok = refl

-- Dodecahedron (金) → I_h
dodV : ℤ; dodV = + 20
dodE : ℤ; dodE = + 30
dodF : ℤ; dodF = + 12
dodChi : ℤ; dodChi = dodV - dodE + dodF
dodChi-ok : dodChi ≡ + 2; dodChi-ok = refl

-- Icosahedron (水) → I
icoV : ℤ; icoV = + 12
icoE : ℤ; icoE = + 30
icoF : ℤ; icoF = + 20
icoChi : ℤ; icoChi = icoV - icoE + icoF
icoChi-ok : icoChi ≡ + 2; icoChi-ok = refl

-- 群阶 (ℕ)
groupOrderA4  : ℕ; groupOrderA4  = 12
groupOrderOh  : ℕ; groupOrderOh  = 48
groupOrderO   : ℕ; groupOrderO   = 24
groupOrderIh  : ℕ; groupOrderIh  = 120
groupOrderI   : ℕ; groupOrderI   = 60
