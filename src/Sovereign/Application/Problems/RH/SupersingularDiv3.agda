{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.SupersingularDiv3
-- Waterhouse q=3 判据的「p∣t」算术表述桥（M6 · B4）
--
-- 数学背景:
--   Waterhouse 定理的算术形式: E/F_p 超奇异 ⟺ p ∣ t（Frobenius 迹被 p 整除）。
--   本件把该表述与迹集表述（IsSup ↔ t ∈ {−3,0,+3}，WaterhouseF3.water-iff）桥接:
--   Div3V v（迹值 v 被 3 整除）⟺ v ∈ {trM3, trZ, trP3}，故
--   · div3V-sup: 3∣t（值层）⟹ IsSup c（经 water-bwd）
--   · sup-div3V: IsSup c ⟹ 3∣t（值层）（经 sup-trace + val-inj 归值）
--   ⟹ 「p∣t」表述不再是纯定义选择: 两方向都与代数定义无关地可证,
--      判据的两个等价表述（整除式/迹集式）在同一套定义下互推。
--
-- 诚实边界（Deuring 正常元线, 见 docs/Riemann A5.2 注记）:
--   「p∣t ⟺ E 超奇异」的**代数侧**（E[3](F̄₃) 破灭 / End⊗ℚ 四元数 /
--   Deuring 正常元 ρ²=−3）需要 E(F₉) 群律 + 端环载体——库内 0 命中, 未排期。
--   本桥升级的是「表述等价」, 不是 Deuring 定理本身。
--   σ-组合载体（Fix(σ) = #E(F₃) 等）见 FrobF9/FrobFix 线。

module Sovereign.Application.Problems.RH.SupersingularDiv3 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Sovereign.Application.Problems.RH.CurveF3
open import Sovereign.Application.Problems.RH.CountF3
open import Sovereign.Application.Problems.RH.TraceTableF3
open import Sovereign.Application.Problems.RH.SupersingularF3
open import Sovereign.Application.Problems.RH.WaterhouseF3

--------------------------------------------------------------------------------
-- §1. 迹值整除层: Div3V v ⟺ v ∈ {trM3, trZ, trP3}
--------------------------------------------------------------------------------

Div3V : Tr3 → Set
Div3V trM3 = ⊤
Div3V trM2 = ⊥
Div3V trM1 = ⊥
Div3V trZ  = ⊤
Div3V trP1 = ⊥
Div3V trP2 = ⊥
Div3V trP3 = ⊤

-- Div3V v 持有 ⟹ v 是三个超奇异迹值之一
div3V-cls : ∀ (v : Tr3) → Div3V v
         → (v ≡ trM3) ⊎ ((v ≡ trZ) ⊎ (v ≡ trP3))
div3V-cls trM3 d = inj₁ refl
div3V-cls trZ  d = inj₂ (inj₁ refl)
div3V-cls trP3 d = inj₂ (inj₂ refl)
div3V-cls trM2 ()
div3V-cls trM1 ()
div3V-cls trP1 ()
div3V-cls trP2 ()

--------------------------------------------------------------------------------
-- §2. 双向桥（值层承载; tval 由 trace-in-Tr3 全覆盖给出）
--------------------------------------------------------------------------------

-- 3∣t（值层）⟹ IsSup c（经 water-bwd; val trM3/-trZ/-trP3 ≡ −3/+0/+3 定义归约）
div3V-sup : ∀ (c : CurveF3) (h : IsNonSing c) (v : Tr3)
          → tℤ c ≡ val v → Div3V v → IsSup c
div3V-sup c h v tval d with div3V-cls v d
... | inj₁ e = water-bwd c h (inj₁ (trans tval (cong val e)))
... | inj₂ (inj₁ e) = water-bwd c h (inj₂ (inj₁ (trans tval (cong val e))))
... | inj₂ (inj₂ e) = water-bwd c h (inj₂ (inj₂ (trans tval (cong val e))))

-- IsSup c ⟹ 3∣t（值层）（经 sup-trace 三分支 + val-inj 归值）
sup-div3V : ∀ (c : CurveF3) (h : IsNonSing c) (v : Tr3)
          → tℤ c ≡ val v → IsSup c → Div3V v
sup-div3V c h v tval s with sup-trace c s
... | inj₁ e = subst Div3V (sym (val-inj v trM3 (trans (sym tval) e))) tt
... | inj₂ (inj₁ e) = subst Div3V (sym (val-inj v trZ (trans (sym tval) e))) tt
... | inj₂ (inj₂ e) = subst Div3V (sym (val-inj v trP3 (trans (sym tval) e))) tt

-- 组合桥（∀④ 的整除表述版）: 3∣t ⟺ IsSup, 任取迹值代表 v
div3V-supΣ : ∀ (c : CurveF3) (h : IsNonSing c)
           → Σ Tr3 (λ v → tℤ c ≡ val v × Div3V v) → IsSup c
div3V-supΣ c h (v , tval , d) = div3V-sup c h v tval d

sup-div3VΣ : ∀ (c : CurveF3) (h : IsNonSing c)
           → IsSup c → Σ Tr3 (λ v → tℤ c ≡ val v × Div3V v)
sup-div3VΣ c h s = proj₁ (trace-in-Tr3 c h) ,
                   proj₂ (trace-in-Tr3 c h) ,
                   sup-div3V c h (proj₁ (trace-in-Tr3 c h))
                            (proj₂ (trace-in-Tr3 c h)) s
