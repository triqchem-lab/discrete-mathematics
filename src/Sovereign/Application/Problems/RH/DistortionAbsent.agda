{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.DistortionAbsent
-- M11·N4: rho-候选 (x,y) ↦ (−x, α·y) 于普通 4 类缺席（候选级构造性见证）
--
-- 数学背景（oracle endordinary 冻结, 先算后验）:
--   · 超奇异侧（EndDistortion0/5）: rho 是真自同态（a₆=0 类）
--   · 普通侧: 代表元全部 a₆ ≠ 0 ⟹ 封闭恒等式 (α·y)² = rhs(−x) 即失败 ——
--     Deuring 对照的第二半: 普通类上「同一候选」连曲线映射都不是
--   · 每类一条 absurd: LHS = f9mul (mula y) (mula y) 归约字面 ≠ RHS = rhs9 c (fneg x) 归约字面
--
-- 诚实边界 [构造性缺席·候选级]:
--   · 本件只证 rho-候选映射于普通类缺席; 「End(E) 的 F₉-有理部分 = ℤ[π]」的
--     全域陈述不作（需要对全体候选映射的量化, 未形式化）
--   · 数值子句全部 oracle endordinary 生成（先算后验纪律）

module Sovereign.Application.Problems.RH.DistortionAbsent where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Application.Problems.RH.CurveF3
  using (CurveF3; mkC; c101; c102; c201; c202)
open import Sovereign.Application.Problems.RH.CountF9All
  using (F9; mkF9; f9add; f9mul; rhs9)

--------------------------------------------------------------------------------
-- §0. rho-候选的坐标层件（fneg 全分量求负; mula = α·_）
--------------------------------------------------------------------------------

fneg : F9 → F9
fneg (mkF9 a b) = mkF9 (negate a) (negate b)

mula : F9 → F9
mula (mkF9 c d) = mkF9 (negate d) c

--------------------------------------------------------------------------------
-- §1. cls1（c101, t=-2）: 见证点 (mkF9 T₀ T₀, mkF9 T₁ T₀) —— 全域 7 点封闭失败, 此为首见
--------------------------------------------------------------------------------

rho-abs-cls1 : f9mul (mula (mkF9 T₁ T₀)) (mula (mkF9 T₁ T₀)) ≡ rhs9 c101 (fneg (mkF9 T₀ T₀)) → ⊥
rho-abs-cls1 ()

--------------------------------------------------------------------------------
-- §2. cls2（c102, t=+1）: 见证点 (mkF9 T₀ T₀, mkF9 T₀ T₁) —— 全域 10 点封闭失败, 此为首见
--------------------------------------------------------------------------------

rho-abs-cls2 : f9mul (mula (mkF9 T₀ T₁)) (mula (mkF9 T₀ T₁)) ≡ rhs9 c102 (fneg (mkF9 T₀ T₀)) → ⊥
rho-abs-cls2 ()

--------------------------------------------------------------------------------
-- §3. cls3（c201, t=-1）: 见证点 (mkF9 T₀ T₀, mkF9 T₁ T₀) —— 全域 10 点封闭失败, 此为首见
--------------------------------------------------------------------------------

rho-abs-cls3 : f9mul (mula (mkF9 T₁ T₀)) (mula (mkF9 T₁ T₀)) ≡ rhs9 c201 (fneg (mkF9 T₀ T₀)) → ⊥
rho-abs-cls3 ()

--------------------------------------------------------------------------------
-- §4. cls4（c202, t=+2）: 见证点 (mkF9 T₀ T₀, mkF9 T₀ T₁) —— 全域 7 点封闭失败, 此为首见
--------------------------------------------------------------------------------

rho-abs-cls4 : f9mul (mula (mkF9 T₀ T₁)) (mula (mkF9 T₀ T₁)) ≡ rhs9 c202 (fneg (mkF9 T₀ T₀)) → ⊥
rho-abs-cls4 ()

