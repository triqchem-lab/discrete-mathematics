{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.SupersingularF3
-- F₃ 曲线的超奇异分类（M3 · A3.1）
--
-- 数学背景:
--   q = p（素域）情形的 Waterhouse 刻画: E/Fₚ 超奇异 ⟺ p ∣ t（Frobenius 迹被 p 整除）。
--   本模块把该刻画作为**定义选择**（标注: 是「定义 + oracle 交叉核对」，不是被证明的
--   深层定理——深层证明需要 Deuring 正常元（库内 0 命中，见九项清单第 8 项））。
--   F₃ 上迹集为 Tr3 的 7 值（TraceTableF3），其中被 3 整除的恰 3 值:
--   {−3, 0, +3} —— 即 trM3 / trZ / trP3。
--
-- 实现: 迹值函数 trV c = vOf (pointsE c)（vOf 把 #E ∈ {1..7} 映到 Tr3 的 7 值，
--   4 ↦ trZ 对应 t = 4 − 4 = 0 等）；IsSup c := SupV (trV c)，其中 SupV 对
--   trM3/trZ/trP3 给 ⊤、其余给 ⊥。IsSup 是**可判定**定义（无 Σ/命题包装），
--   因此下游（ZetaAllF3 的零点刚性）分派时各分支可定义性归约。
--
-- 本模块证明（0 postulate，全部 refl/tt/⊥-elim）:
--   §1 vOf / trV / SupV / IsSup（定义层）
--   §2 **∀③-a**: 6 条超奇异曲线的见证（c010/c011/c012/c020/c021/c022）
--   §3 **∀③-b**: sup-trace —— IsSup c ⟹ tℤ c ∈ {−3, 0, +3}（27 构造子分派）
--
-- 诚实边界: §2+§3 合起来是「迹集 = {−3,0,3}」的双向；「每个值恰一个同构类」
--   属 Waterhouse 细分类，不在本件（值级只到 TraceTableF3）。

module Sovereign.Application.Problems.RH.SupersingularF3 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Application.Problems.RH.CurveF3
open import Sovereign.Application.Problems.RH.CountF3
open import Sovereign.Application.Problems.RH.TraceTableF3

--------------------------------------------------------------------------------
-- §1. 迹值抽取与超奇异性判定（定义层）
--------------------------------------------------------------------------------

-- #E ∈ {1..7} → 迹值 {+3,+2,+1,0,−1,−2,−3}（1↦+3 … 7↦−3；越界退化归 trZ）
vOf : ℕ → Tr3
vOf zero = trZ
vOf (suc zero) = trP3
vOf (suc (suc zero)) = trP2
vOf (suc (suc (suc zero))) = trP1
vOf (suc (suc (suc (suc zero)))) = trZ
vOf (suc (suc (suc (suc (suc zero))))) = trM1
vOf (suc (suc (suc (suc (suc (suc zero)))))) = trM2
vOf (suc (suc (suc (suc (suc (suc (suc zero))))))) = trM3
vOf (suc (suc (suc (suc (suc (suc (suc (suc _)))))))) = trZ

trV : CurveF3 → Tr3
trV c = vOf (pointsE c)

-- 超奇异迹值: {−3, 0, +3}（Waterhouse q=p 刻画的定义选择, 见头注）
SupV : Tr3 → Set
SupV trM3 = ⊤
SupV trM2 = ⊥
SupV trM1 = ⊥
SupV trZ  = ⊤
SupV trP1 = ⊥
SupV trP2 = ⊥
SupV trP3 = ⊤

IsSup : CurveF3 → Set
IsSup c = SupV (trV c)

--------------------------------------------------------------------------------
-- §2. ∀③-a: 6 条超奇异曲线的见证
--------------------------------------------------------------------------------

isSup-c010 : IsSup c010
isSup-c010 = tt
isSup-c011 : IsSup c011
isSup-c011 = tt
isSup-c012 : IsSup c012
isSup-c012 = tt
isSup-c020 : IsSup c020
isSup-c020 = tt
isSup-c021 : IsSup c021
isSup-c021 = tt
isSup-c022 : IsSup c022
isSup-c022 = tt

--------------------------------------------------------------------------------
-- §3. ∀③-b: IsSup c ⟹ tℤ c ∈ {−3, 0, +3}
--------------------------------------------------------------------------------

sup-trace : ∀ (c : CurveF3) → IsSup c →
  (tℤ c ≡ -[1+ 2 ]) ⊎ ((tℤ c ≡ + 0) ⊎ (tℤ c ≡ + 3))
sup-trace (mkC T₀ T₀ T₀) s = inj₂ (inj₁ refl)  -- #4, t=+ 0, trV=trZ T
sup-trace (mkC T₀ T₀ T₁) s = inj₂ (inj₁ refl)  -- #4, t=+ 0, trV=trZ T
sup-trace (mkC T₀ T₀ T₂) s = inj₂ (inj₁ refl)  -- #4, t=+ 0, trV=trZ T
sup-trace (mkC T₀ T₁ T₀) s = inj₂ (inj₁ refl)  -- #4, t=+ 0, trV=trZ T
sup-trace (mkC T₀ T₁ T₁) s = inj₂ (inj₁ refl)  -- #4, t=+ 0, trV=trZ T
sup-trace (mkC T₀ T₁ T₂) s = inj₂ (inj₁ refl)  -- #4, t=+ 0, trV=trZ T
sup-trace (mkC T₀ T₂ T₀) s = inj₂ (inj₁ refl)  -- #4, t=+ 0, trV=trZ T
sup-trace (mkC T₀ T₂ T₁) s = inj₁ refl  -- #7, t=−3, trV=trM3 T
sup-trace (mkC T₀ T₂ T₂) s = inj₂ (inj₂ refl)  -- #1, t=+ 3, trV=trP3 T
sup-trace (mkC T₁ T₀ T₀) s = ⊥-elim s  -- #3, t=+ 1, trV=trP1 ⊥
sup-trace (mkC T₁ T₀ T₁) s = ⊥-elim s  -- #6, t=−2, trV=trM2 ⊥
sup-trace (mkC T₁ T₀ T₂) s = ⊥-elim s  -- #3, t=+ 1, trV=trP1 ⊥
sup-trace (mkC T₁ T₁ T₀) s = ⊥-elim s  -- #3, t=+ 1, trV=trP1 ⊥
sup-trace (mkC T₁ T₁ T₁) s = ⊥-elim s  -- #6, t=−2, trV=trM2 ⊥
sup-trace (mkC T₁ T₁ T₂) s = ⊥-elim s  -- #3, t=+ 1, trV=trP1 ⊥
sup-trace (mkC T₁ T₂ T₀) s = ⊥-elim s  -- #6, t=−2, trV=trM2 ⊥
sup-trace (mkC T₁ T₂ T₁) s = ⊥-elim s  -- #3, t=+ 1, trV=trP1 ⊥
sup-trace (mkC T₁ T₂ T₂) s = ⊥-elim s  -- #3, t=+ 1, trV=trP1 ⊥
sup-trace (mkC T₂ T₀ T₀) s = ⊥-elim s  -- #5, t=−1, trV=trM1 ⊥
sup-trace (mkC T₂ T₀ T₁) s = ⊥-elim s  -- #5, t=−1, trV=trM1 ⊥
sup-trace (mkC T₂ T₀ T₂) s = ⊥-elim s  -- #2, t=+ 2, trV=trP2 ⊥
sup-trace (mkC T₂ T₁ T₀) s = ⊥-elim s  -- #5, t=−1, trV=trM1 ⊥
sup-trace (mkC T₂ T₁ T₁) s = ⊥-elim s  -- #5, t=−1, trV=trM1 ⊥
sup-trace (mkC T₂ T₁ T₂) s = ⊥-elim s  -- #2, t=+ 2, trV=trP2 ⊥
sup-trace (mkC T₂ T₂ T₀) s = ⊥-elim s  -- #2, t=+ 2, trV=trP2 ⊥
sup-trace (mkC T₂ T₂ T₁) s = ⊥-elim s  -- #5, t=−1, trV=trM1 ⊥
sup-trace (mkC T₂ T₂ T₂) s = ⊥-elim s  -- #5, t=−1, trV=trM1 ⊥
