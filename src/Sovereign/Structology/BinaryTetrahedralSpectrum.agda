{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.BinaryTetrahedralSpectrum
-- 谱的显式处理: 阶 → 特征值 → 迹 = 特征标 (0 postulate)
--
-- 填补表示论缺口「谱定理的有限域版」: 有限群表示的特征值由元素阶数决定,
-- 特征标 = 特征值之和。SL(2,3) 二维定义表示的特征值:
--   阶 1 → {1,1},  阶 2 → {-1,-1},  阶 3 → {ω,ω²},
--   阶 4 → {i,-i},  阶 6 → {-ω,-ω²}
-- 特征值之和 (迹) 落在 Z[ω] (i 分量相消), 即 χ₂。
-- 本模块把特征值显式写出 (在 Z[ω,i] 中), 证明其和 = 由阶数推导的 χ₂,
-- 使 Zωi 环落到其本来的用途 (4 阶元素的 ±i 特征值)。

module Sovereign.Structology.BinaryTetrahedralSpectrum where

open import Data.Nat using (ℕ)
open import Data.Integer.Base using (+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.Zωi
  using (Zωi; mkZωi; zeroZωi; oneZωi; ωZωi; iZωi; addZωi; negZωi; mulZωi)
open import Sovereign.Structology.A4Representation using (Zω; mkZω)
open import Sovereign.Structology.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23; orderOf; chi2FromRep)

--------------------------------------------------------------------------------
-- §1. ω² 与特征值谱
--------------------------------------------------------------------------------

ω²Zωi : Zωi
ω²Zωi = mulZωi ωZωi ωZωi

-- 阶 → 特征值对 (在 Z[ω,i] 中)
spectrum : ℕ → Zωi × Zωi
spectrum 1 = oneZωi , oneZωi
spectrum 2 = negZωi oneZωi , negZωi oneZωi
spectrum 3 = ωZωi , ω²Zωi
spectrum 4 = iZωi , negZωi iZωi
spectrum 6 = negZωi ωZωi , negZωi ω²Zωi
spectrum _ = oneZωi , oneZωi   -- 不可达

-- 特征值之和 = 迹
sumSpectrum : ℕ → Zωi
sumSpectrum n = addZωi (proj₁ (spectrum n)) (proj₂ (spectrum n))

-- Z[ω] → Z[ω,i] 嵌入 (c=d=0)
embed : Zω → Zωi
embed (mkZω a b) = mkZωi a b (+ 0) (+ 0)

--------------------------------------------------------------------------------
-- §2. 谱恒等式 (特征值之和, i 分量相消)
--------------------------------------------------------------------------------

omega-sum-neg-one : addZωi ωZωi ω²Zωi ≡ negZωi oneZωi   -- ω + ω² = -1
omega-sum-neg-one = refl

i-sum-zero : addZωi iZωi (negZωi iZωi) ≡ zeroZωi         -- i + (-i) = 0
i-sum-zero = refl

negomega-sum-one : addZωi (negZωi ωZωi) (negZωi ω²Zωi) ≡ oneZωi  -- -ω - ω² = 1
negomega-sum-one = refl

--------------------------------------------------------------------------------
-- §3. 主定理: 特征标 = 特征值之和 (24 refl)
--------------------------------------------------------------------------------

spectrum-correct : ∀ (g : SL23) → sumSpectrum (orderOf g) ≡ embed (chi2FromRep g)
spectrum-correct g0 = refl
spectrum-correct g1 = refl
spectrum-correct g2 = refl
spectrum-correct g3 = refl
spectrum-correct g4 = refl
spectrum-correct g5 = refl
spectrum-correct g6 = refl
spectrum-correct g7 = refl
spectrum-correct g8 = refl
spectrum-correct g9 = refl
spectrum-correct g10 = refl
spectrum-correct g11 = refl
spectrum-correct g12 = refl
spectrum-correct g13 = refl
spectrum-correct g14 = refl
spectrum-correct g15 = refl
spectrum-correct g16 = refl
spectrum-correct g17 = refl
spectrum-correct g18 = refl
spectrum-correct g19 = refl
spectrum-correct g20 = refl
spectrum-correct g21 = refl
spectrum-correct g22 = refl
spectrum-correct g23 = refl

-- 0 postulate.

--------------------------------------------------------------------------------
-- L2 结构定理 (全称量化)
--------------------------------------------------------------------------------

-- L2: 特征值和恒等式
omega-sum : addZωi ωZωi ω²Zωi ≡ negZωi oneZωi
omega-sum = omega-sum-neg-one

i-sum : addZωi iZωi (negZωi iZωi) ≡ zeroZωi
i-sum = i-sum-zero

negomega-sum : addZωi (negZωi ωZωi) (negZωi ω²Zωi) ≡ oneZωi
negomega-sum = negomega-sum-one

-- L2: 谱定理总结 (5 个阶的特征值和)
spectrum-summary :
  (sumSpectrum 1 ≡ embed (chi2FromRep g6))
  × (sumSpectrum 2 ≡ embed (chi2FromRep g15))
  × (sumSpectrum 3 ≡ embed (chi2FromRep g2))
  × (sumSpectrum 4 ≡ embed (chi2FromRep g0))
  × (sumSpectrum 6 ≡ embed (chi2FromRep g1))
spectrum-summary = refl , refl , refl , refl , refl
