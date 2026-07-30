--
-- 本模块是 HFM 交叉验证测试向量, 不替代原形式化证明。
-- 主证明见: WuXingTransition.agda
{-# OPTIONS --rewriting #-}

-- | Sovereign.Structology.WuXingEulerHFM
-- 柏拉图立体 Euler 示性数的 HFM 交叉验证

module Sovereign.Structology.WuXingEulerHFM where

open import Data.Integer using (ℤ; +_; -_; _+_; _-_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning

-- 正四面体 V=4, E=6, F=4 -> chi = 2
tetV : ℤ; tetV = + 4; tetE : ℤ; tetE = + 6; tetF : ℤ; tetF = + 4
tetChi : ℤ; tetChi = tetV - tetE + tetF
tetChi-ok : tetChi ≡ + 2
tetChi-ok = begin tetChi ≡⟨⟩ (+ 4) - (+ 6) + (+ 4) ≡⟨⟩ (-(+ 2)) + (+ 4) ≡⟨⟩ (+ 2) ∎

-- 正六面体 V=8, E=12, F=6 -> chi = 2
cubeV : ℤ; cubeV = + 8; cubeE : ℤ; cubeE = + 12; cubeF : ℤ; cubeF = + 6
cubeChi : ℤ; cubeChi = cubeV - cubeE + cubeF
cubeChi-ok : cubeChi ≡ + 2
cubeChi-ok = begin cubeChi ≡⟨⟩ (+ 8) - (+ 12) + (+ 6) ≡⟨⟩ (-(+ 4)) + (+ 6) ≡⟨⟩ (+ 2) ∎

-- 正八面体 V=6, E=12, F=8 -> chi = 2
octV : ℤ; octV = + 6; octE : ℤ; octE = + 12; octF : ℤ; octF = + 8
octChi : ℤ; octChi = octV - octE + octF
octChi-ok : octChi ≡ + 2
octChi-ok = begin octChi ≡⟨⟩ (+ 6) - (+ 12) + (+ 8) ≡⟨⟩ (-(+ 6)) + (+ 8) ≡⟨⟩ (+ 2) ∎

-- 正十二面体 V=20, E=30, F=12 -> chi = 2
dodV : ℤ; dodV = + 20; dodE : ℤ; dodE = + 30; dodF : ℤ; dodF = + 12
dodChi : ℤ; dodChi = dodV - dodE + dodF
dodChi-ok : dodChi ≡ + 2
dodChi-ok = begin dodChi ≡⟨⟩ (+ 20) - (+ 30) + (+ 12) ≡⟨⟩ (-(+ 10)) + (+ 12) ≡⟨⟩ (+ 2) ∎

-- 正二十面体 V=12, E=30, F=20 -> chi = 2
icoV : ℤ; icoV = + 12; icoE : ℤ; icoE = + 30; icoF : ℤ; icoF = + 20
icoChi : ℤ; icoChi = icoV - icoE + icoF
icoChi-ok : icoChi ≡ + 2
icoChi-ok = begin icoChi ≡⟨⟩ (+ 12) - (+ 30) + (+ 20) ≡⟨⟩ (-(+ 18)) + (+ 20) ≡⟨⟩ (+ 2) ∎
