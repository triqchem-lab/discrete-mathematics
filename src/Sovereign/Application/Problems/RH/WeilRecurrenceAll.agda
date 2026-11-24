{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.WeilRecurrenceAll
-- Weil 递推全称化: ∀⑤ t₂ = t₁² − 2q（q = 3）+ ∀BSD9（M4 · A4.2）
--
-- 数学背景:
--   Weil 递推: E/F_q 上 t(F_{q²}) = t(F_q)² − 2q。q = 3 即 t₂ = t₁² − 6。
--   语义形 t₁² − 2q（+ 2 * + 3）；数值由封闭归约给出，与 oracle emit9 的
--   (t₁,t₂) 18 行对照表逐行一致（t₂ = t₁²−6 校验 18/18 True, 2026-11-24）。
--   ∀BSD9: #E(F₉) = q + 1 − t₂ = 10 − t₂（点侧形式，WeilRigidity 三条
--   bsd-identity-*-9 的 18 条全称化）。
--
-- 证明骨架（0 postulate，27 形状分派 × 2 定理）:
--   9 奇异分支: IsNonSing 假设真用（⊥-elim (h refl)）;
--   18 非奇异分支: refl（c 具体化后两侧封闭归约; t2ℤ/b2n 链见 CountF9All）。
--
-- 与旧件交叉一致: c011(E₁) t₂=−6、c021(E₂) t₂=+3、c022(E₆) t₂=+3
-- （WeilRigidity t2-E1/E2/E6）。

module Sovereign.Application.Problems.RH.WeilRecurrenceAll where

open import Data.Empty using (⊥-elim)
open import Data.Integer using (ℤ; +_; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Application.Problems.RH.CurveF3
open import Sovereign.Application.Problems.RH.CountF3
open import Sovereign.Application.Problems.RH.CountF9All

--------------------------------------------------------------------------------
-- §1. F₉ 迹（ℤ 层）
--------------------------------------------------------------------------------

-- t₂ = q + 1 − #E(F₉)，q = 9
t2ℤ : CurveF3 → ℤ
t2ℤ c = + 10 - + (pointsE9 c)

--------------------------------------------------------------------------------
-- §2. ∀⑤: t₂ = t₁² − 2q（q = 3）
--------------------------------------------------------------------------------

recurrence-all : ∀ (c : CurveF3) → IsNonSing c →
  t2ℤ c ≡ (tℤ c * tℤ c) - (+ 2 * + 3)
-- 9 奇异形状
recurrence-all (mkC T₀ T₀ T₀) h = ⊥-elim (h refl)
recurrence-all (mkC T₀ T₀ T₁) h = ⊥-elim (h refl)
recurrence-all (mkC T₀ T₀ T₂) h = ⊥-elim (h refl)
recurrence-all (mkC T₁ T₀ T₀) h = ⊥-elim (h refl)
recurrence-all (mkC T₁ T₁ T₀) h = ⊥-elim (h refl)
recurrence-all (mkC T₁ T₂ T₂) h = ⊥-elim (h refl)
recurrence-all (mkC T₂ T₀ T₀) h = ⊥-elim (h refl)
recurrence-all (mkC T₂ T₁ T₀) h = ⊥-elim (h refl)
recurrence-all (mkC T₂ T₂ T₁) h = ⊥-elim (h refl)
-- 18 非奇异形状（封闭归约; 数值对照 = oracle emit9 §(t₁,t₂) 表）
recurrence-all (mkC T₀ T₁ T₀) h = refl
recurrence-all (mkC T₀ T₁ T₁) h = refl
recurrence-all (mkC T₀ T₁ T₂) h = refl
recurrence-all (mkC T₀ T₂ T₀) h = refl
recurrence-all (mkC T₀ T₂ T₁) h = refl
recurrence-all (mkC T₀ T₂ T₂) h = refl
recurrence-all (mkC T₁ T₀ T₁) h = refl
recurrence-all (mkC T₁ T₀ T₂) h = refl
recurrence-all (mkC T₁ T₁ T₁) h = refl
recurrence-all (mkC T₁ T₁ T₂) h = refl
recurrence-all (mkC T₁ T₂ T₀) h = refl
recurrence-all (mkC T₁ T₂ T₁) h = refl
recurrence-all (mkC T₂ T₀ T₁) h = refl
recurrence-all (mkC T₂ T₀ T₂) h = refl
recurrence-all (mkC T₂ T₁ T₁) h = refl
recurrence-all (mkC T₂ T₁ T₂) h = refl
recurrence-all (mkC T₂ T₂ T₀) h = refl
recurrence-all (mkC T₂ T₂ T₂) h = refl

--------------------------------------------------------------------------------
-- §3. ∀BSD9: #E(F₉) = 10 − t₂（q+1−t₂ 的 q=9 全称化）
--------------------------------------------------------------------------------

bsd9-all : ∀ (c : CurveF3) → IsNonSing c →
  (+ 10) - t2ℤ c ≡ + (pointsE9 c)
-- 9 奇异形状
bsd9-all (mkC T₀ T₀ T₀) h = ⊥-elim (h refl)
bsd9-all (mkC T₀ T₀ T₁) h = ⊥-elim (h refl)
bsd9-all (mkC T₀ T₀ T₂) h = ⊥-elim (h refl)
bsd9-all (mkC T₁ T₀ T₀) h = ⊥-elim (h refl)
bsd9-all (mkC T₁ T₁ T₀) h = ⊥-elim (h refl)
bsd9-all (mkC T₁ T₂ T₂) h = ⊥-elim (h refl)
bsd9-all (mkC T₂ T₀ T₀) h = ⊥-elim (h refl)
bsd9-all (mkC T₂ T₁ T₀) h = ⊥-elim (h refl)
bsd9-all (mkC T₂ T₂ T₁) h = ⊥-elim (h refl)
-- 18 非奇异形状（封闭归约; 与 WeilRigidity bsd-identity-*-9 三例一致: 16/7/7）
bsd9-all (mkC T₀ T₁ T₀) h = refl
bsd9-all (mkC T₀ T₁ T₁) h = refl
bsd9-all (mkC T₀ T₁ T₂) h = refl
bsd9-all (mkC T₀ T₂ T₀) h = refl
bsd9-all (mkC T₀ T₂ T₁) h = refl
bsd9-all (mkC T₀ T₂ T₂) h = refl
bsd9-all (mkC T₁ T₀ T₁) h = refl
bsd9-all (mkC T₁ T₀ T₂) h = refl
bsd9-all (mkC T₁ T₁ T₁) h = refl
bsd9-all (mkC T₁ T₁ T₂) h = refl
bsd9-all (mkC T₁ T₂ T₀) h = refl
bsd9-all (mkC T₁ T₂ T₁) h = refl
bsd9-all (mkC T₂ T₀ T₁) h = refl
bsd9-all (mkC T₂ T₀ T₂) h = refl
bsd9-all (mkC T₂ T₁ T₁) h = refl
bsd9-all (mkC T₂ T₁ T₂) h = refl
bsd9-all (mkC T₂ T₂ T₀) h = refl
bsd9-all (mkC T₂ T₂ T₂) h = refl
