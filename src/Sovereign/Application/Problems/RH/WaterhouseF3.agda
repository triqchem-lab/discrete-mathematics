{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.WaterhouseF3
-- q = p Waterhouse 判据的 F₃ 包装件（M3 · A3.2）
--
-- 数学背景:
--   Waterhouse（q=p 定义选择, 见 SupersingularF3 头注）: E/Fₚ 超奇异 ⟺ p ∣ t。
--   q = 3 时 Hasse 界内 t ∈ {−3,…,+3}，被 3 整除的恰 {−3, 0, +3}
--   —— 即 Tr3 的 trM3 / trZ / trP3（值层承载整除分类, 见 SupV）。
--
-- 本模块证明（0 postulate，全部 refl/tt/⊥-elim/val-inj 分派）:
--   §1 值层引理  val3→sup : val v ∈ {−3,0,+3} ⟹ SupV v
--      （12 条构造子互斥 ⊥ 引理 + 15 构造子分派；⟸ 方向无 —— SupV 的 ⊥
--       分支没有居留者可从 ≡ 造出，反向 iff 由 §3 的 Σ 配对在曲线层完成）
--   §2 ∀④-bwd   water-bwd : t ∈ {−3,0,+3} ⟹ IsSup c
--      （trace-in-Tr3 全覆盖 + val3-of 转接 + val3→sup）
--   §3 合成      water-iff : IsSup ↔ t ∈ {−3,0,+3}
--      （⟹ 复用 SupersingularF3.sup-trace；⟸ 本件 §2）
--   §4 ∀④-exist water-surj : 每个 Tr3 迹值都有非奇异曲线实现
--      （TraceTableF3.trace-witness 直接别名 —— 见证表不重复造）
--
-- 诚实边界:
--   · 「3 ∣ t」在本件以「t 落入 {−3,0,+3}（Tr3 的 3 值子集）」承载；
--     Hasse 界（∀①）保证界内两者等价，故 §3 即 p∣t 判据的 q=3 全称形式。
--   · 「每个值恰对应一个同构类」属 Waterhouse 细分类，不在本件
--     （需同构分类，值级只到 TraceTableF3，同 TraceTableF3 头注边界）。
--   · 未使用的签名级显式参数在本库 Agda 2.9.0-nightly 下触发
--     UnsolvedMetaVariables（2026-11-24 NormClassify 探针二分实证），
--     故本件所有签名显式参数均在体内出现。

module Sovereign.Application.Problems.RH.WaterhouseF3 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Application.Problems.RH.CurveF3
open import Sovereign.Application.Problems.RH.CountF3
open import Sovereign.Application.Problems.RH.TraceTableF3
open import Sovereign.Application.Problems.RH.SupersingularF3

--------------------------------------------------------------------------------
-- §1. 值层: 构造子互斥 ⊥ 引理（12 条; ≡ 型 absurd, 同 val-inj 机制）
--------------------------------------------------------------------------------

neMM : trM2 ≡ trM3 → ⊥
neMM ()
neMZ : trM2 ≡ trZ → ⊥
neMZ ()
neMP : trM2 ≡ trP3 → ⊥
neMP ()
ne1M : trM1 ≡ trM3 → ⊥
ne1M ()
ne1Z : trM1 ≡ trZ → ⊥
ne1Z ()
ne1P : trM1 ≡ trP3 → ⊥
ne1P ()
nePM : trP1 ≡ trM3 → ⊥
nePM ()
nePZ : trP1 ≡ trZ → ⊥
nePZ ()
nePP : trP1 ≡ trP3 → ⊥
nePP ()
ne2M : trP2 ≡ trM3 → ⊥
ne2M ()
ne2Z : trP2 ≡ trZ → ⊥
ne2Z ()
ne2P : trP2 ≡ trP3 → ⊥
ne2P ()
-- 超奇异 3 值的假分支方向（val3→sup 21 全覆盖所需）
neM3Z : trM3 ≡ trZ → ⊥
neM3Z ()
neM3P : trM3 ≡ trP3 → ⊥
neM3P ()
neZM3 : trZ ≡ trM3 → ⊥
neZM3 ()
neZP3 : trZ ≡ trP3 → ⊥
neZP3 ()
neP3M : trP3 ≡ trM3 → ⊥
neP3M ()
neP3Z : trP3 ≡ trZ → ⊥
neP3Z ()

--------------------------------------------------------------------------------
-- §1b. 值层主引理: val v 落在 {−3,0,+3} ⟹ SupV v
--------------------------------------------------------------------------------

val3→sup : ∀ (v : Tr3) →
  (val v ≡ val trM3) ⊎ ((val v ≡ + 0) ⊎ (val v ≡ + 3)) → SupV v
-- 超奇异 3 值: ⊤ 分支
val3→sup trM3 (inj₁ e) = tt
val3→sup trZ  (inj₂ (inj₁ e)) = tt
val3→sup trP3 (inj₂ (inj₂ e)) = tt
-- 超奇异 3 值的假分支: val-inj 互斥
val3→sup trM3 (inj₂ (inj₁ e)) = ⊥-elim (neM3Z (val-inj trM3 trZ e))
val3→sup trM3 (inj₂ (inj₂ e)) = ⊥-elim (neM3P (val-inj trM3 trP3 e))
val3→sup trZ  (inj₁ e) = ⊥-elim (neZM3 (val-inj trZ trM3 e))
val3→sup trZ  (inj₂ (inj₂ e)) = ⊥-elim (neZP3 (val-inj trZ trP3 e))
val3→sup trP3 (inj₁ e) = ⊥-elim (neP3M (val-inj trP3 trM3 e))
val3→sup trP3 (inj₂ (inj₁ e)) = ⊥-elim (neP3Z (val-inj trP3 trZ e))
-- 非超奇异 4 值 × 3 分支: val-inj 后构造子互斥
val3→sup trM2 (inj₁ e) = ⊥-elim (neMM (val-inj trM2 trM3 e))
val3→sup trM2 (inj₂ (inj₁ e)) = ⊥-elim (neMZ (val-inj trM2 trZ e))
val3→sup trM2 (inj₂ (inj₂ e)) = ⊥-elim (neMP (val-inj trM2 trP3 e))
val3→sup trM1 (inj₁ e) = ⊥-elim (ne1M (val-inj trM1 trM3 e))
val3→sup trM1 (inj₂ (inj₁ e)) = ⊥-elim (ne1Z (val-inj trM1 trZ e))
val3→sup trM1 (inj₂ (inj₂ e)) = ⊥-elim (ne1P (val-inj trM1 trP3 e))
val3→sup trP1 (inj₁ e) = ⊥-elim (nePM (val-inj trP1 trM3 e))
val3→sup trP1 (inj₂ (inj₁ e)) = ⊥-elim (nePZ (val-inj trP1 trZ e))
val3→sup trP1 (inj₂ (inj₂ e)) = ⊥-elim (nePP (val-inj trP1 trP3 e))
val3→sup trP2 (inj₁ e) = ⊥-elim (ne2M (val-inj trP2 trM3 e))
val3→sup trP2 (inj₂ (inj₁ e)) = ⊥-elim (ne2Z (val-inj trP2 trZ e))
val3→sup trP2 (inj₂ (inj₂ e)) = ⊥-elim (ne2P (val-inj trP2 trP3 e))

-- 转接: t 层三分假设 + tval ⟹ 值层三分
val3-of : ∀ (v : Tr3) (t : ℤ) → t ≡ val v →
  (t ≡ val trM3) ⊎ ((t ≡ + 0) ⊎ (t ≡ + 3)) →
  (val v ≡ val trM3) ⊎ ((val v ≡ + 0) ⊎ (val v ≡ + 3))
val3-of v t tval (inj₁ e) = inj₁ (trans (sym tval) e)
val3-of v t tval (inj₂ (inj₁ e)) = inj₂ (inj₁ (trans (sym tval) e))
val3-of v t tval (inj₂ (inj₂ e)) = inj₂ (inj₂ (trans (sym tval) e))

--------------------------------------------------------------------------------
-- §2. ∀④-bwd: t ∈ {−3,0,+3} ⟹ IsSup c（全称）
--------------------------------------------------------------------------------

water-bwd : ∀ (c : CurveF3) → IsNonSing c →
  (tℤ c ≡ -[1+ 2 ]) ⊎ ((tℤ c ≡ + 0) ⊎ (tℤ c ≡ + 3)) → IsSup c
-- 9 奇异形状: 非奇异性假设直接矛盾（目标可居留但不走假门）
water-bwd (mkC T₀ T₀ T₀) h hyp = ⊥-elim (h refl)
water-bwd (mkC T₀ T₀ T₁) h hyp = ⊥-elim (h refl)
water-bwd (mkC T₀ T₀ T₂) h hyp = ⊥-elim (h refl)
water-bwd (mkC T₁ T₀ T₀) h hyp = ⊥-elim (h refl)
water-bwd (mkC T₁ T₁ T₀) h hyp = ⊥-elim (h refl)
water-bwd (mkC T₁ T₂ T₂) h hyp = ⊥-elim (h refl)
water-bwd (mkC T₂ T₀ T₀) h hyp = ⊥-elim (h refl)
water-bwd (mkC T₂ T₁ T₀) h hyp = ⊥-elim (h refl)
water-bwd (mkC T₂ T₂ T₁) h hyp = ⊥-elim (h refl)
-- 6 超奇异形状: SupV = ⊤（trV 逐形状定义归约: c010-c012/c020 ↦ trZ, c021 ↦ trM3, c022 ↦ trP3）
water-bwd (mkC T₀ T₁ T₀) h hyp = tt
water-bwd (mkC T₀ T₁ T₁) h hyp = tt
water-bwd (mkC T₀ T₁ T₂) h hyp = tt
water-bwd (mkC T₀ T₂ T₀) h hyp = tt
water-bwd (mkC T₀ T₂ T₁) h hyp = tt
water-bwd (mkC T₀ T₂ T₂) h hyp = tt
-- 12 非超奇异形状: tval = refl（定义归约）+ val3-of 转接 + val3→sup
water-bwd (mkC T₁ T₀ T₁) h hyp =
  val3→sup trM2 (val3-of trM2 (tℤ (mkC T₁ T₀ T₁)) refl hyp)
water-bwd (mkC T₁ T₀ T₂) h hyp =
  val3→sup trP1 (val3-of trP1 (tℤ (mkC T₁ T₀ T₂)) refl hyp)
water-bwd (mkC T₁ T₁ T₁) h hyp =
  val3→sup trM2 (val3-of trM2 (tℤ (mkC T₁ T₁ T₁)) refl hyp)
water-bwd (mkC T₁ T₁ T₂) h hyp =
  val3→sup trP1 (val3-of trP1 (tℤ (mkC T₁ T₁ T₂)) refl hyp)
water-bwd (mkC T₁ T₂ T₀) h hyp =
  val3→sup trM2 (val3-of trM2 (tℤ (mkC T₁ T₂ T₀)) refl hyp)
water-bwd (mkC T₁ T₂ T₁) h hyp =
  val3→sup trP1 (val3-of trP1 (tℤ (mkC T₁ T₂ T₁)) refl hyp)
water-bwd (mkC T₂ T₀ T₁) h hyp =
  val3→sup trM1 (val3-of trM1 (tℤ (mkC T₂ T₀ T₁)) refl hyp)
water-bwd (mkC T₂ T₀ T₂) h hyp =
  val3→sup trP2 (val3-of trP2 (tℤ (mkC T₂ T₀ T₂)) refl hyp)
water-bwd (mkC T₂ T₁ T₁) h hyp =
  val3→sup trM1 (val3-of trM1 (tℤ (mkC T₂ T₁ T₁)) refl hyp)
water-bwd (mkC T₂ T₁ T₂) h hyp =
  val3→sup trP2 (val3-of trP2 (tℤ (mkC T₂ T₁ T₂)) refl hyp)
water-bwd (mkC T₂ T₂ T₀) h hyp =
  val3→sup trP2 (val3-of trP2 (tℤ (mkC T₂ T₂ T₀)) refl hyp)
water-bwd (mkC T₂ T₂ T₂) h hyp =
  val3→sup trM1 (val3-of trM1 (tℤ (mkC T₂ T₂ T₂)) refl hyp)

--------------------------------------------------------------------------------
-- §3. 合成: IsSup ↔ t ∈ {−3,0,+3}（⟹ 复用 sup-trace; ⟸ 本件 §2）
--------------------------------------------------------------------------------

water-iff : ∀ (c : CurveF3) → IsNonSing c →
  ( IsSup c → ((tℤ c ≡ -[1+ 2 ]) ⊎ ((tℤ c ≡ + 0) ⊎ (tℤ c ≡ + 3))))
  × ( ((tℤ c ≡ -[1+ 2 ]) ⊎ ((tℤ c ≡ + 0) ⊎ (tℤ c ≡ + 3))) → IsSup c )
water-iff c h = ( sup-trace c , water-bwd c h )

--------------------------------------------------------------------------------
-- §4. ∀④-exist: 界内每迹可实现（TraceTableF3 §3 见证表别名, 不重复造表）
--------------------------------------------------------------------------------

water-surj : ∀ (v : Tr3) → Σ CurveF3 (λ c → IsNonSing c × tℤ c ≡ val v)
water-surj = trace-witness
