{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.BinaryTetrahedralTwoDimTensors
-- 2·A₄ 的另外两个二维不可约表示: χ₂′ 与 χ₂″ 的张量积推导 (0 postulate)
--
-- 深度证明 (与 BinaryTetrahedralDefiningRep 组成完整链):
--   χ₂  = 定义表示 (GF(3) 矩阵, 阶数 → 迹)     [BinaryTetrahedralDefiningRep]
--   χ₂′ = χ₂ ⊗ χ₁′  (定义表示 ⊗ ω 特征)       [本模块]
--   χ₂″ = χ₂ ⊗ χ₁″  (定义表示 ⊗ ω² 特征)      [本模块]
-- 其中 χ₁′、χ₁″ 是一维表示 (abelianization A₄→C₃ 的 ω、ω² 特征, 见 A4OneDimHom)。
--
-- 故三个二维不可约表示的特征标均由构造导出, 不再是手写表:
--   二维表示 ≅ 定义表示 ⊗ {1, χ₁′, χ₁″} (三维张量积分解)。
-- Z[ω,i] 的 i 分量在迹中消去, 特征标落在 Z[ω]。

module Sovereign.Structology.BinaryTetrahedralTwoDimTensors where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.A4Representation using (Zω; mulZω)
open import Sovereign.Structology.BinaryTetrahedralRepresentation
  using (ConjClass2A4; chi1'-2A4; chi1''-2A4; chi2-2A4; chi2'-2A4; chi2''-2A4)

--------------------------------------------------------------------------------
-- §1. χ₂′ = χ₂ ⊗ χ₁′  (定义表示与 ω 特征的张量积)
--------------------------------------------------------------------------------

chi2'-tensor : ∀ (c : ConjClass2A4) →
  chi2'-2A4 c ≡ mulZω (chi2-2A4 c) (chi1'-2A4 c)
chi2'-tensor zero = refl
chi2'-tensor (suc zero) = refl
chi2'-tensor (suc (suc zero)) = refl
chi2'-tensor (suc (suc (suc zero))) = refl
chi2'-tensor (suc (suc (suc (suc zero)))) = refl
chi2'-tensor (suc (suc (suc (suc (suc zero))))) = refl
chi2'-tensor (suc (suc (suc (suc (suc (suc zero)))))) = refl

--------------------------------------------------------------------------------
-- §2. χ₂″ = χ₂ ⊗ χ₁″  (定义表示与 ω² 特征的张量积)
--------------------------------------------------------------------------------

chi2''-tensor : ∀ (c : ConjClass2A4) →
  chi2''-2A4 c ≡ mulZω (chi2-2A4 c) (chi1''-2A4 c)
chi2''-tensor zero = refl
chi2''-tensor (suc zero) = refl
chi2''-tensor (suc (suc zero)) = refl
chi2''-tensor (suc (suc (suc zero))) = refl
chi2''-tensor (suc (suc (suc (suc zero)))) = refl
chi2''-tensor (suc (suc (suc (suc (suc zero))))) = refl
chi2''-tensor (suc (suc (suc (suc (suc (suc zero)))))) = refl

-- 0 postulate.
