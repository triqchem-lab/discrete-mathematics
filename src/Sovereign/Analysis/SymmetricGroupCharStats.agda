{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.SymmetricGroupCharStats
-- 62-10 群表示统计 — A₄ 的 Plancherel 分布与特征标期望 (0 postulate)
--
-- Plancherel 分布: P(λ) = (dim λ)²/|G| — 整数权重 w(λ) = dim λ²
-- 中心特征标期望 = 列正交关系 (第一正交关系):
--   E_planch[χ_λ(g)/dim λ] = Σ_λ dim λ·χ_λ(g)/|G| = δ(g=e)
--   (整数形式: Σ dim·χ(g) = |G| 于 e, = 0 于其余类)
-- 行正交 (第二正交关系实例): Σ_C |C|·χ(C)·conj(χ(C)) = |G| (每不可约)
-- 载体 = A₄ (类 1/4/4/3, 特征标值 ∈ Z[ω] — 1+ω+ω²=0 承载列正交)

module Sovereign.Analysis.SymmetricGroupCharStats where

open import Data.Product using (_×_; _,_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.A4Group using (A4; Id; Rot; Flip)
open import Sovereign.Structology.A4Representations using
  (A4Irrep; V1; V1'; V1''; V3; dim; character; dimSqSum)
import Sovereign.RootMath.Eisenstein as Eis

-- 局部 Z[ω] 算子
_⊞_ : Eis.Eisenstein → Eis.Eisenstein → Eis.Eisenstein
_⊞_ = Eis._+ᵉ_

_⊠_ : Eis.Eisenstein → Eis.Eisenstein → Eis.Eisenstein
_⊠_ = Eis._*ᵉ_

infixl 20 _⊞_ ; infixl 25 _⊠_

--------------------------------------------------------------------------------
-- §1. Plancherel 权重: w(λ) = (dim λ)² — Σ w = |A₄| = 12 (引用)
--------------------------------------------------------------------------------

w1  w1'  w1''  w3 : Eis.Eisenstein
w1  = Eis.1ᵉ          -- dim V1²  = 1
w1' = Eis.1ᵉ          -- dim V1'² = 1
w1'' = Eis.1ᵉ         -- dim V1''² = 1
w3  = Eis.3ᵉ ⊠ Eis.3ᵉ  -- dim V3²  = 9

-- Plancherel 归一: Σ w = 12 = |A₄| (与 dimSqSum 一致, Z[ω] 形式)
plancherel-normalized : w1 ⊞ w1' ⊞ w1'' ⊞ w3 ≡ Eis.eis (+ 12) (+ 0)
plancherel-normalized = refl

--------------------------------------------------------------------------------
-- §2. 中心特征标期望 (列正交): Σ_λ dim·χ_λ(g) = 12·δ(g=e)
--------------------------------------------------------------------------------

-- C1 (单位元): 1·1 + 1·1 + 1·1 + 3·3 = 12
col-C1 : (Eis.1ᵉ ⊠ character V1 Id)
       ⊞ (Eis.1ᵉ ⊠ character V1' Id)
       ⊞ (Eis.1ᵉ ⊠ character V1'' Id)
       ⊞ (Eis.3ᵉ ⊠ character V3 Id) ≡ Eis.eis (+ 12) (+ 0)
col-C1 = refl

-- C2 (3-循环, χ₁' = ω): 1 + ω + ω² + 3·0 = 0 (1+ω+ω²=0)
col-C2 : (Eis.1ᵉ ⊠ character V1 (Rot fz fz))
       ⊞ (Eis.1ᵉ ⊠ character V1' (Rot fz fz))
       ⊞ (Eis.1ᵉ ⊠ character V1'' (Rot fz fz))
       ⊞ (Eis.3ᵉ ⊠ character V3 (Rot fz fz)) ≡ Eis.0ᵉ
col-C2 = refl

-- C3 (另一 3-循环, χ₁' = ω²): 1 + ω² + ω + 0 = 0
col-C3 : (Eis.1ᵉ ⊠ character V1 (Rot fz (fs fz)))
       ⊞ (Eis.1ᵉ ⊠ character V1' (Rot fz (fs fz)))
       ⊞ (Eis.1ᵉ ⊠ character V1'' (Rot fz (fs fz)))
       ⊞ (Eis.3ᵉ ⊠ character V3 (Rot fz (fs fz))) ≡ Eis.0ᵉ
col-C3 = refl

-- C4 (二重对换, χ₃ = −1): 1 + 1 + 1 + 3·(−1) = 0
col-C4 : (Eis.1ᵉ ⊠ character V1 (Flip fz))
       ⊞ (Eis.1ᵉ ⊠ character V1' (Flip fz))
       ⊞ (Eis.1ᵉ ⊠ character V1'' (Flip fz))
       ⊞ (Eis.3ᵉ ⊠ character V3 (Flip fz)) ≡ Eis.0ᵉ
col-C4 = refl

-- 期望形式: E_planch[χ/dim] = δ(g=e) — 上四式的统计解释
-- (Plancherel 权重 (dim λ)² 与中心特征标 χ/dim 的配对 = 列正交)

--------------------------------------------------------------------------------
-- §3. 行正交 (第二正交关系实例): Σ_C |C|·χ(C)·conj(χ(C)) = 12
--------------------------------------------------------------------------------

-- 类大小: C1=1, C2=4, C3=4, C4=3 — 各不可约的行正交:
-- V1 (全 1): 1·1 + 4·1 + 4·1 + 3·1 = 12
row-V1 : (Eis.1ᵉ ⊠ Eis.1ᵉ ⊠ Eis.1ᵉ)
       ⊞ ((Eis.eis (+ 4) (+ 0)) ⊠ Eis.1ᵉ ⊠ Eis.1ᵉ)
       ⊞ ((Eis.eis (+ 4) (+ 0)) ⊠ Eis.1ᵉ ⊠ Eis.1ᵉ)
       ⊞ (Eis.3ᵉ ⊠ Eis.1ᵉ ⊠ Eis.1ᵉ) ≡ Eis.eis (+ 12) (+ 0)
row-V1 = refl

-- V3 (3,0,0,−1): 1·9 + 4·0 + 4·0 + 3·1 = 12
row-V3 : (Eis.1ᵉ ⊠ Eis.3ᵉ ⊠ Eis.3ᵉ)
       ⊞ ((Eis.eis (+ 4) (+ 0)) ⊠ Eis.0ᵉ ⊠ Eis.0ᵉ)
       ⊞ ((Eis.eis (+ 4) (+ 0)) ⊠ Eis.0ᵉ ⊠ Eis.0ᵉ)
       ⊞ (Eis.3ᵉ ⊠ Eis.-1ᵉ ⊠ Eis.-1ᵉ) ≡ Eis.eis (+ 12) (+ 0)
row-V3 = refl

-- V1' (1,ω,ω²,1): 1·1 + 4·ω·ω² + 4·ω²·ω + 3·1 = 1+4+4+3 = 12 (ω³=1)
row-V1' : (Eis.1ᵉ ⊠ Eis.1ᵉ ⊠ Eis.1ᵉ)
        ⊞ ((Eis.eis (+ 4) (+ 0)) ⊠ Eis.ωᵉ ⊠ Eis.ω²ᵉ)
        ⊞ ((Eis.eis (+ 4) (+ 0)) ⊠ Eis.ω²ᵉ ⊠ Eis.ωᵉ)
        ⊞ (Eis.3ᵉ ⊠ Eis.1ᵉ ⊠ Eis.1ᵉ) ≡ Eis.eis (+ 12) (+ 0)
row-V1' = refl

-- V1'' (1,ω²,ω,1): 同上 (共轭对)
row-V1'' : (Eis.1ᵉ ⊠ Eis.1ᵉ ⊠ Eis.1ᵉ)
         ⊞ ((Eis.eis (+ 4) (+ 0)) ⊠ Eis.ω²ᵉ ⊠ Eis.ωᵉ)
         ⊞ ((Eis.eis (+ 4) (+ 0)) ⊠ Eis.ωᵉ ⊠ Eis.ω²ᵉ)
         ⊞ (Eis.3ᵉ ⊠ Eis.1ᵉ ⊠ Eis.1ᵉ) ≡ Eis.eis (+ 12) (+ 0)
row-V1'' = refl

-- 0 postulate.
