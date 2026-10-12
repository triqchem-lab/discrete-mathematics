{-# OPTIONS --cubical --rewriting --guardedness #-}
-- | _PM7c — GAP-M7b-homology-iso 探针：quasi-iso ⟹ 同调同构
--
-- 数学背景：链同伦等价（quasi-iso）的离散形 = 一对相互尊重（respectful）
--   映射 f : C → D、g : D → C 于商面同伦互逆（g∘f ≃ id、f∘g ≃ id——HR/HS 级
--   同伦见证）。商面消去给出诱导映射对 f̅ : C/HR → D/HS、g̅ : D/HS → C/HR，
--   同伦见证经 eq/ 提升为互逆等式 ⇒ f̅、g̅ 互为逆 ⇒ 同调同构。
--   经典语境：链映射对 + 链同伦 ⟹ Hₖ 同构——本件为其商面级离散形；
--   链级（∂-交换图 + 链同伦到商面同伦的下降）为一般形立界件。
--
-- 核心原则：
--   1. 前提范式：尊重性（f-resp/g-resp）与同伦见证（h/k）显式参数化——
--      同态律类前提不硬证（HRWells/Inst 先例同族）
--   2. 复用零重证：_PM7a 的 HomologyQuotient/HR 面 + _PM7b 的 K3Full 实例件
--   3. 恒等 quasi-iso 的 K₃ 实例核对（defeq 级 refl——诱导映射在 [_] 上计算律）
--   4. 零 with；隐式钉参；诚实立界（一般链复形机件不硬拱）
--
-- 包含：ChainRespectful · HomologyIso（主定理模块：homology-iso）·
--       K3Instance（恒等 quasi-iso 实例 + 核对层）
module _PM7c where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/)
open import Cubical.HITs.SetQuotients.Properties using (rec; elimProp)
open import Cubical.Foundations.Isomorphism using (Iso; iso)

import _PM7a
open import _PM7b using (sub₃; zero₃)

-- ────────────────────────────────────────────────────────────────────
-- §1 HomologyIso 主定理模块（quasi-iso 离散形 → 商面同构）
-- ────────────────────────────────────────────────────────────────────
module HomologyIso
  (C D : Set)
  (HR : C → C → Set)
  (HS : D → D → Set)
  (f : C → D)
  (g : D → C)
  (f-resp : ∀ x y → HR x y → HS (f x) (f y))
  (g-resp : ∀ x y → HS x y → HR (g x) (g y))
  (h : ∀ x → HR (g (f x)) x)
  (k : ∀ y → HS (f (g y)) y)
  where

  -- 诱导映射（尊重性经 rec 提升到商面——HD/HC 均为 set 由 squash/ 承载）
  f̅ : C / HR → D / HS
  f̅ = rec squash/ (λ x → [ f x ]) (λ x y r → eq/ (f x) (f y) (f-resp x y r))

  g̅ : D / HS → C / HR
  g̅ = rec squash/ (λ y → [ g y ]) (λ x y r → eq/ (g x) (g y) (g-resp x y r))

  -- 生成元上互逆（同伦见证经 eq/ 提升）
  f̅g̅-gen : ∀ y → f̅ (g̅ [ y ]) ≡ [ y ]
  f̅g̅-gen y = eq/ (f (g y)) y (k y)

  g̅f̅-gen : ∀ x → g̅ (f̅ [ x ]) ≡ [ x ]
  g̅f̅-gen x = eq/ (g (f x)) x (h x)

  -- 全称提升（商面消去——motive 显式钉，路径在 set 中为 prop）
  HDset : isSet (D / HS)
  HDset = squash/

  HCset : isSet (C / HR)
  HCset = squash/

  f̅g̅ : ∀ y → f̅ (g̅ y) ≡ y
  f̅g̅ = elimProp {P = λ y → f̅ (g̅ y) ≡ y} (λ y → HDset (f̅ (g̅ y)) y) f̅g̅-gen

  g̅f̅ : ∀ x → g̅ (f̅ x) ≡ x
  g̅f̅ = elimProp {P = λ x → g̅ (f̅ x) ≡ x} (λ x → HCset (g̅ (f̅ x)) x) g̅f̅-gen

  -- 主定理：商面同调同构（quasi-iso ⟹ iso）
  homology-iso : Iso (C / HR) (D / HS)
  homology-iso = iso f̅ g̅ f̅g̅ g̅f̅

-- ────────────────────────────────────────────────────────────────────
-- §2 K₃ 恒等 quasi-iso 实例（尊重性/同伦见证均由 hr-refl-k3 承载）
-- ────────────────────────────────────────────────────────────────────
open import Sovereign.Application.FreeAbBoundary using (C₀; C₁; C₂; ∂₁; ∂₂)

module K3Instance
  (comp0-k3 : (c : C₂) → ∂₁ (∂₂ c) ≡ zero₃)
  where

  open _PM7b.K3Full comp0-k3 using (hr-refl-k3)
  open _PM7a.HomologyQuotient C₁ C₀ C₂ sub₃ ∂₁ zero₃ ∂₂ comp0-k3 using (HR)

  -- 恒等映射对（尊重性 = 恒等搬运；同伦见证 = hr-refl）
  id-resp : ∀ x y → HR x y → HR x y
  id-resp x y r = r

  open HomologyIso _ _ HR HR (λ x → x) (λ x → x) id-resp id-resp
    (λ x → hr-refl-k3 x) (λ x → hr-refl-k3 x)
    public

  -- 核对层：诱导映射在生成元上的计算律（defeq 级——rec 于 [_] 归约）
  check-f̅-gen : ∀ x → f̅ [ x ] ≡ [ x ]
  check-f̅-gen x = refl

  check-g̅f̅-gen : ∀ x → g̅ (f̅ [ x ]) ≡ [ x ]
  check-g̅f̅-gen x = refl

  check-iso-both : ∀ x → f̅g̅ [ x ] ≡ f̅g̅-gen x
  check-iso-both x = refl
