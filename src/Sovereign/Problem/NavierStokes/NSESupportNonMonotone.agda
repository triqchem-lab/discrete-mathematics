{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSESupportNonMonotone
-- **supportCount 在 nsStep 下非单调**（双向见证）—— O3 通道 ⑤ 单调性问题的**判定**
--
-- 主定理（本模块）:
--   `not-nondecreasing : ¬ (∀ v → supportCount v ≤ supportCount (nsStep v))`
--     （**收缩见证** witnessField: 17 → 14）
--   `not-nonincreasing : ¬ (∀ v → supportCount (nsStep v) ≤ supportCount v)`
--     （**增长见证** growField: 243 → 1458）
--   ⇒ supportCount **既非单调不减、也非单调不增** ⇒ 「集中度单调发展」型机制**不存在**。
--
-- 收缩见证的构造（配对抵消 + 单对做 g 的源）:
--   配对 (1,4): v₄ = −v₁；配对 (2,5): v₅ = −v₂；**源对 (3,6)**: v₃ = C（一点丘）, v₆ = 0
--   ⇒ g = div v = D₂C（其余两对的贡献自反抵消）；取 v₁ := D₀g、v₂ := D₁g
--   ⇒ 演化后两配对各归零一半（comp4' = comp5' = 0）, 全场 17 → 14。
--   ⚠ 手算教训（编译纠正）: D₂²C 是**常场** (T₁,T₁,T₁)（D₂³ = 0 的相容形）——
--     我漏了一处 `T₂ ⊕ T₂ = T₁`, 曾把 comp3'/comp6' 算成 2 点（实为 3 点）。
--
-- 判型注: 计数为**表事实的 refl**（表 vs 公式 ⇒ 穷举就是内容, pair-popping.md §2 反例行）;
--   排序引理 `lt-plus`（自备 4 行）—— 均非配对弹出族。
--
-- 0 postulate / 0 hole

module Sovereign.Problem.NavierStokes.NSESupportNonMonotone where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6; mkField; diffF; nsStep)
open import Sovereign.Problem.NavierStokes.NSEFixedPointStrict using
  (countOver; supportCount)

--------------------------------------------------------------------------------
-- §1. 见证场
--------------------------------------------------------------------------------

zeroS : ScalarField
zeroS _ = T₀

negF : ScalarField → ScalarField
negF f x = negate (f x)

-- 增长见证: 仅 x₁ = 0 切片取 T₁（e₁-不变）
growF : ScalarField
growF (fzero , _ , _ , _ , _ , _) = T₁
growF _                          = T₀

growField : Field
growField = mkField growF zeroS zeroS zeroS zeroS zeroS

-- 收缩见证: 一点丘 C（T₁ 于原点）+ 配对抵消结构
cF : ScalarField
cF (fzero , fzero , fzero , fzero , fzero , fzero) = T₁
cF _                                               = T₀

gF : ScalarField
gF = diffF (fsuc (fsuc fzero)) cF                    -- g := D₂C

witnessField : Field
witnessField = mkField
  (diffF fzero gF) (diffF (fsuc fzero) gF) cF        -- v₁ := D₀g, v₂ := D₁g, v₃ := C
  (negF (diffF fzero gF)) (negF (diffF (fsuc fzero) gF)) zeroS
                                                    -- v₄ := −v₁, v₅ := −v₂, v₆ := 0

--------------------------------------------------------------------------------
-- §2. 计数（表事实 refl；分量级便于出错定位）
--------------------------------------------------------------------------------

-- 增长见证: 243 → 1458
grow-before : supportCount growField ≡ 243
grow-before = refl

grow-after : supportCount (nsStep growField) ≡ 1458
grow-after = refl

-- 收缩见证: 17 → 14（分量: 4/4/1/4/4/0 → 4/4/3/0/0/3）
wit-before : supportCount witnessField ≡ 17
wit-before = refl

wit-after : supportCount (nsStep witnessField) ≡ 14
wit-after = refl

wit-q-v3 : countOver (v3 (nsStep witnessField)) ≡ 3
wit-q-v3 = refl

wit-q-v6 : countOver (v6 (nsStep witnessField)) ≡ 3
wit-q-v6 = refl

--------------------------------------------------------------------------------
-- §3. 排序小引理（自备）与**主定理**
--------------------------------------------------------------------------------

-- 和严格大于被加数: `m + suc k ≤ m` 不可能
lt-plus : ∀ m k → ¬ (m + suc k ≤ m)
lt-plus zero    k ()
lt-plus (suc m) k (s≤s p) = lt-plus m k p

split-wit : 14 + suc 2 ≡ 17
split-wit = refl

split-grow : 243 + suc 1214 ≡ 1458
split-grow = refl

-- 主定理（一）: supportCount **不是**单调不减的
not-nondecreasing : ¬ (∀ v → supportCount v ≤ supportCount (nsStep v))
not-nondecreasing hyp =
  lt-plus 14 2
    (subst (λ z → z ≤ 14) (sym split-wit)
      (subst (λ z → 17 ≤ z) wit-after
        (subst (λ z → z ≤ supportCount (nsStep witnessField)) wit-before
          (hyp witnessField))))

-- 主定理（二）: supportCount **不是**单调不增的
not-nonincreasing : ¬ (∀ v → supportCount (nsStep v) ≤ supportCount v)
not-nonincreasing hyp =
  lt-plus 243 1214
    (subst (λ z → z ≤ 243) (sym split-grow)
      (subst (λ z → 1458 ≤ z) grow-before
        (subst (λ z → z ≤ supportCount growField) grow-after
          (hyp growField))))

-- **判定**: 两个方向的单调性主张均被否定
support-nonmonotone :
  (¬ (∀ v → supportCount v ≤ supportCount (nsStep v)))
  × (¬ (∀ v → supportCount (nsStep v) ≤ supportCount v))
support-nonmonotone = not-nondecreasing , not-nonincreasing

--------------------------------------------------------------------------------
-- §4. 诚实边界
--
-- ✓ 已证: 增长见证（243→1458）/ 收缩见证（17→14）/ **双向非单调判定**。
--   ⇒ O3 通道 ⑤ 的「集中度单调发展」型机制**不存在**；四件套 + 判定齐:
--   定义 ✓ 界 ✓ 零元刻画 ✓ 不动点不变性 ✓ **单调性判定 ✓（非单调）**。
-- ✗ 不声称:
--   ① 「非单调 ⇒ 无集中」**不成立**——波动式集中仍可能（本模块只否定单调机制）;
--   ② supportCount 的**动力学分布**（各计数值的轨道结构）未刻画;
--   ③ 连续统 NS 的任何结论。
--------------------------------------------------------------------------------
