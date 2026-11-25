{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.EndDistortion0
-- Deuring 失真映射 rho 于 cls0（c010, 超奇异 t=0）—— End(E) ⊋ Z[σ]-作用的第一砖
--
-- 数学背景（oracle distortion 冻结, 先算后验）:
--   · rho : (x,y) ↦ (-x, α·y)（α² = -1 ∈ F₉）; 经典 Deuring 失真映射（CM by Z[i] 谱系）
--   · 曲线封闭 + rho(P+Q) = rho P + rho Q（**256 对 hom**）+ rho² = neg
--   · **σρ = −ρσ**（反交换; Galois 共轭作用于 CM: σρσ = −ρ —— 手算 σρ=ρσ 被枚举否证）
--   · **rho ∉ Z[σ]-作用**: 作用映射 P ↦ [a]P + [b]·σP（a,b ∈ {0..3}; σ²=id, [4]=0 点级
--     定案合法域）去重后逐个与 rho 有分离点 —— 超奇异 ⟹ End(E) 超出 Z[π]-作用的
--     **构造性离散见证**（End(E) 环论层首件; 完整四元序分类不作陈述）
--
-- 诚实边界:
--   · 本件是点级映射层的分离定理; 「End(E) 是四元代数序」的完整环论表述不作陈述
--   · 数值子句全部 oracle distortion 生成（先算后验纪律）

module Sovereign.Application.Problems.RH.EndDistortion0 where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Application.Problems.RH.GroupCls0

--------------------------------------------------------------------------------
-- §1. rho 表（oracle 逐字; 16 点）
--------------------------------------------------------------------------------

rho : Pt0 → Pt0
rho ptInf = ptInf
rho pt1 = pt1
rho pt2 = pt3
rho pt3 = pt2
rho pt4 = pt11
rho pt5 = pt10
rho pt6 = pt15
rho pt7 = pt14
rho pt8 = pt13
rho pt9 = pt12
rho pt10 = pt4
rho pt11 = pt5
rho pt12 = pt8
rho pt13 = pt9
rho pt14 = pt6
rho pt15 = pt7

--------------------------------------------------------------------------------
-- §2. 作用映射承件: act0/act1 具名（[0]=ptInf, [1]=id; mul2/mul3 复用 GroupCls0）
--------------------------------------------------------------------------------

act0 : Pt0 → Pt0
act0 _ = ptInf

act1 : Pt0 → Pt0
act1 p = p

--------------------------------------------------------------------------------
-- §3. rho² = neg 与 rhoσ = σρ（16 + 16 条）
--------------------------------------------------------------------------------

rho-sq-neg : ∀ p → rho (rho p) ≡ negp p
rho-sq-neg ptInf = refl
rho-sq-neg pt1 = refl
rho-sq-neg pt2 = refl
rho-sq-neg pt3 = refl
rho-sq-neg pt4 = refl
rho-sq-neg pt5 = refl
rho-sq-neg pt6 = refl
rho-sq-neg pt7 = refl
rho-sq-neg pt8 = refl
rho-sq-neg pt9 = refl
rho-sq-neg pt10 = refl
rho-sq-neg pt11 = refl
rho-sq-neg pt12 = refl
rho-sq-neg pt13 = refl
rho-sq-neg pt14 = refl
rho-sq-neg pt15 = refl

rho-sig-anticomm : ∀ p → sig (rho p) ≡ negp (rho (sig p))
rho-sig-anticomm ptInf = refl
rho-sig-anticomm pt1 = refl
rho-sig-anticomm pt2 = refl
rho-sig-anticomm pt3 = refl
rho-sig-anticomm pt4 = refl
rho-sig-anticomm pt5 = refl
rho-sig-anticomm pt6 = refl
rho-sig-anticomm pt7 = refl
rho-sig-anticomm pt8 = refl
rho-sig-anticomm pt9 = refl
rho-sig-anticomm pt10 = refl
rho-sig-anticomm pt11 = refl
rho-sig-anticomm pt12 = refl
rho-sig-anticomm pt13 = refl
rho-sig-anticomm pt14 = refl
rho-sig-anticomm pt15 = refl

--------------------------------------------------------------------------------
-- §4. ★ 256 对 hom: rho (p + q) ≡ rho p + rho q（End(E) 成员判据）
--------------------------------------------------------------------------------

rho-hom : ∀ p q → rho (addE p q) ≡ addE (rho p) (rho q)
rho-hom ptInf ptInf = refl
rho-hom ptInf pt1 = refl
rho-hom ptInf pt2 = refl
rho-hom ptInf pt3 = refl
rho-hom ptInf pt4 = refl
rho-hom ptInf pt5 = refl
rho-hom ptInf pt6 = refl
rho-hom ptInf pt7 = refl
rho-hom ptInf pt8 = refl
rho-hom ptInf pt9 = refl
rho-hom ptInf pt10 = refl
rho-hom ptInf pt11 = refl
rho-hom ptInf pt12 = refl
rho-hom ptInf pt13 = refl
rho-hom ptInf pt14 = refl
rho-hom ptInf pt15 = refl
rho-hom pt1 ptInf = refl
rho-hom pt1 pt1 = refl
rho-hom pt1 pt2 = refl
rho-hom pt1 pt3 = refl
rho-hom pt1 pt4 = refl
rho-hom pt1 pt5 = refl
rho-hom pt1 pt6 = refl
rho-hom pt1 pt7 = refl
rho-hom pt1 pt8 = refl
rho-hom pt1 pt9 = refl
rho-hom pt1 pt10 = refl
rho-hom pt1 pt11 = refl
rho-hom pt1 pt12 = refl
rho-hom pt1 pt13 = refl
rho-hom pt1 pt14 = refl
rho-hom pt1 pt15 = refl
rho-hom pt2 ptInf = refl
rho-hom pt2 pt1 = refl
rho-hom pt2 pt2 = refl
rho-hom pt2 pt3 = refl
rho-hom pt2 pt4 = refl
rho-hom pt2 pt5 = refl
rho-hom pt2 pt6 = refl
rho-hom pt2 pt7 = refl
rho-hom pt2 pt8 = refl
rho-hom pt2 pt9 = refl
rho-hom pt2 pt10 = refl
rho-hom pt2 pt11 = refl
rho-hom pt2 pt12 = refl
rho-hom pt2 pt13 = refl
rho-hom pt2 pt14 = refl
rho-hom pt2 pt15 = refl
rho-hom pt3 ptInf = refl
rho-hom pt3 pt1 = refl
rho-hom pt3 pt2 = refl
rho-hom pt3 pt3 = refl
rho-hom pt3 pt4 = refl
rho-hom pt3 pt5 = refl
rho-hom pt3 pt6 = refl
rho-hom pt3 pt7 = refl
rho-hom pt3 pt8 = refl
rho-hom pt3 pt9 = refl
rho-hom pt3 pt10 = refl
rho-hom pt3 pt11 = refl
rho-hom pt3 pt12 = refl
rho-hom pt3 pt13 = refl
rho-hom pt3 pt14 = refl
rho-hom pt3 pt15 = refl
rho-hom pt4 ptInf = refl
rho-hom pt4 pt1 = refl
rho-hom pt4 pt2 = refl
rho-hom pt4 pt3 = refl
rho-hom pt4 pt4 = refl
rho-hom pt4 pt5 = refl
rho-hom pt4 pt6 = refl
rho-hom pt4 pt7 = refl
rho-hom pt4 pt8 = refl
rho-hom pt4 pt9 = refl
rho-hom pt4 pt10 = refl
rho-hom pt4 pt11 = refl
rho-hom pt4 pt12 = refl
rho-hom pt4 pt13 = refl
rho-hom pt4 pt14 = refl
rho-hom pt4 pt15 = refl
rho-hom pt5 ptInf = refl
rho-hom pt5 pt1 = refl
rho-hom pt5 pt2 = refl
rho-hom pt5 pt3 = refl
rho-hom pt5 pt4 = refl
rho-hom pt5 pt5 = refl
rho-hom pt5 pt6 = refl
rho-hom pt5 pt7 = refl
rho-hom pt5 pt8 = refl
rho-hom pt5 pt9 = refl
rho-hom pt5 pt10 = refl
rho-hom pt5 pt11 = refl
rho-hom pt5 pt12 = refl
rho-hom pt5 pt13 = refl
rho-hom pt5 pt14 = refl
rho-hom pt5 pt15 = refl
rho-hom pt6 ptInf = refl
rho-hom pt6 pt1 = refl
rho-hom pt6 pt2 = refl
rho-hom pt6 pt3 = refl
rho-hom pt6 pt4 = refl
rho-hom pt6 pt5 = refl
rho-hom pt6 pt6 = refl
rho-hom pt6 pt7 = refl
rho-hom pt6 pt8 = refl
rho-hom pt6 pt9 = refl
rho-hom pt6 pt10 = refl
rho-hom pt6 pt11 = refl
rho-hom pt6 pt12 = refl
rho-hom pt6 pt13 = refl
rho-hom pt6 pt14 = refl
rho-hom pt6 pt15 = refl
rho-hom pt7 ptInf = refl
rho-hom pt7 pt1 = refl
rho-hom pt7 pt2 = refl
rho-hom pt7 pt3 = refl
rho-hom pt7 pt4 = refl
rho-hom pt7 pt5 = refl
rho-hom pt7 pt6 = refl
rho-hom pt7 pt7 = refl
rho-hom pt7 pt8 = refl
rho-hom pt7 pt9 = refl
rho-hom pt7 pt10 = refl
rho-hom pt7 pt11 = refl
rho-hom pt7 pt12 = refl
rho-hom pt7 pt13 = refl
rho-hom pt7 pt14 = refl
rho-hom pt7 pt15 = refl
rho-hom pt8 ptInf = refl
rho-hom pt8 pt1 = refl
rho-hom pt8 pt2 = refl
rho-hom pt8 pt3 = refl
rho-hom pt8 pt4 = refl
rho-hom pt8 pt5 = refl
rho-hom pt8 pt6 = refl
rho-hom pt8 pt7 = refl
rho-hom pt8 pt8 = refl
rho-hom pt8 pt9 = refl
rho-hom pt8 pt10 = refl
rho-hom pt8 pt11 = refl
rho-hom pt8 pt12 = refl
rho-hom pt8 pt13 = refl
rho-hom pt8 pt14 = refl
rho-hom pt8 pt15 = refl
rho-hom pt9 ptInf = refl
rho-hom pt9 pt1 = refl
rho-hom pt9 pt2 = refl
rho-hom pt9 pt3 = refl
rho-hom pt9 pt4 = refl
rho-hom pt9 pt5 = refl
rho-hom pt9 pt6 = refl
rho-hom pt9 pt7 = refl
rho-hom pt9 pt8 = refl
rho-hom pt9 pt9 = refl
rho-hom pt9 pt10 = refl
rho-hom pt9 pt11 = refl
rho-hom pt9 pt12 = refl
rho-hom pt9 pt13 = refl
rho-hom pt9 pt14 = refl
rho-hom pt9 pt15 = refl
rho-hom pt10 ptInf = refl
rho-hom pt10 pt1 = refl
rho-hom pt10 pt2 = refl
rho-hom pt10 pt3 = refl
rho-hom pt10 pt4 = refl
rho-hom pt10 pt5 = refl
rho-hom pt10 pt6 = refl
rho-hom pt10 pt7 = refl
rho-hom pt10 pt8 = refl
rho-hom pt10 pt9 = refl
rho-hom pt10 pt10 = refl
rho-hom pt10 pt11 = refl
rho-hom pt10 pt12 = refl
rho-hom pt10 pt13 = refl
rho-hom pt10 pt14 = refl
rho-hom pt10 pt15 = refl
rho-hom pt11 ptInf = refl
rho-hom pt11 pt1 = refl
rho-hom pt11 pt2 = refl
rho-hom pt11 pt3 = refl
rho-hom pt11 pt4 = refl
rho-hom pt11 pt5 = refl
rho-hom pt11 pt6 = refl
rho-hom pt11 pt7 = refl
rho-hom pt11 pt8 = refl
rho-hom pt11 pt9 = refl
rho-hom pt11 pt10 = refl
rho-hom pt11 pt11 = refl
rho-hom pt11 pt12 = refl
rho-hom pt11 pt13 = refl
rho-hom pt11 pt14 = refl
rho-hom pt11 pt15 = refl
rho-hom pt12 ptInf = refl
rho-hom pt12 pt1 = refl
rho-hom pt12 pt2 = refl
rho-hom pt12 pt3 = refl
rho-hom pt12 pt4 = refl
rho-hom pt12 pt5 = refl
rho-hom pt12 pt6 = refl
rho-hom pt12 pt7 = refl
rho-hom pt12 pt8 = refl
rho-hom pt12 pt9 = refl
rho-hom pt12 pt10 = refl
rho-hom pt12 pt11 = refl
rho-hom pt12 pt12 = refl
rho-hom pt12 pt13 = refl
rho-hom pt12 pt14 = refl
rho-hom pt12 pt15 = refl
rho-hom pt13 ptInf = refl
rho-hom pt13 pt1 = refl
rho-hom pt13 pt2 = refl
rho-hom pt13 pt3 = refl
rho-hom pt13 pt4 = refl
rho-hom pt13 pt5 = refl
rho-hom pt13 pt6 = refl
rho-hom pt13 pt7 = refl
rho-hom pt13 pt8 = refl
rho-hom pt13 pt9 = refl
rho-hom pt13 pt10 = refl
rho-hom pt13 pt11 = refl
rho-hom pt13 pt12 = refl
rho-hom pt13 pt13 = refl
rho-hom pt13 pt14 = refl
rho-hom pt13 pt15 = refl
rho-hom pt14 ptInf = refl
rho-hom pt14 pt1 = refl
rho-hom pt14 pt2 = refl
rho-hom pt14 pt3 = refl
rho-hom pt14 pt4 = refl
rho-hom pt14 pt5 = refl
rho-hom pt14 pt6 = refl
rho-hom pt14 pt7 = refl
rho-hom pt14 pt8 = refl
rho-hom pt14 pt9 = refl
rho-hom pt14 pt10 = refl
rho-hom pt14 pt11 = refl
rho-hom pt14 pt12 = refl
rho-hom pt14 pt13 = refl
rho-hom pt14 pt14 = refl
rho-hom pt14 pt15 = refl
rho-hom pt15 ptInf = refl
rho-hom pt15 pt1 = refl
rho-hom pt15 pt2 = refl
rho-hom pt15 pt3 = refl
rho-hom pt15 pt4 = refl
rho-hom pt15 pt5 = refl
rho-hom pt15 pt6 = refl
rho-hom pt15 pt7 = refl
rho-hom pt15 pt8 = refl
rho-hom pt15 pt9 = refl
rho-hom pt15 pt10 = refl
rho-hom pt15 pt11 = refl
rho-hom pt15 pt12 = refl
rho-hom pt15 pt13 = refl
rho-hom pt15 pt14 = refl
rho-hom pt15 pt15 = refl

--------------------------------------------------------------------------------
-- §5. ★ rho ∉ Z[σ]-作用（去重作用映射逐个分离见证）
--------------------------------------------------------------------------------

-- 作用映射 P ↦ [a]P + [b]·σP 即 addE (fA p) (fB (sig p)); fA ∈ {ptInf, id, mul2, mul3}
-- act(0,0) 分离点: pt1
rho-ne-act1 : rho pt1 ≡ addE (act0 pt1) (act0 (sig pt1)) → ⊥
rho-ne-act1 ()
-- act(0,1) 分离点: pt4
rho-ne-act2 : rho pt4 ≡ addE (act0 pt4) (act1 (sig pt4)) → ⊥
rho-ne-act2 ()
-- act(0,2) 分离点: pt1
rho-ne-act3 : rho pt1 ≡ addE (act0 pt1) (mul2 (sig pt1)) → ⊥
rho-ne-act3 ()
-- act(0,3) 分离点: pt4
rho-ne-act4 : rho pt4 ≡ addE (act0 pt4) (mul3 (sig pt4)) → ⊥
rho-ne-act4 ()
-- act(1,0) 分离点: pt2
rho-ne-act5 : rho pt2 ≡ addE (act1 pt2) (act0 (sig pt2)) → ⊥
rho-ne-act5 ()
-- act(1,1) 分离点: pt1
rho-ne-act6 : rho pt1 ≡ addE (act1 pt1) (act1 (sig pt1)) → ⊥
rho-ne-act6 ()
-- act(1,2) 分离点: pt2
rho-ne-act7 : rho pt2 ≡ addE (act1 pt2) (mul2 (sig pt2)) → ⊥
rho-ne-act7 ()
-- act(1,3) 分离点: pt1
rho-ne-act8 : rho pt1 ≡ addE (act1 pt1) (mul3 (sig pt1)) → ⊥
rho-ne-act8 ()
-- act(2,0) 分离点: pt1
rho-ne-act9 : rho pt1 ≡ addE (mul2 pt1) (act0 (sig pt1)) → ⊥
rho-ne-act9 ()
-- act(2,1) 分离点: pt4
rho-ne-act10 : rho pt4 ≡ addE (mul2 pt4) (act1 (sig pt4)) → ⊥
rho-ne-act10 ()
-- act(2,2) 分离点: pt1
rho-ne-act11 : rho pt1 ≡ addE (mul2 pt1) (mul2 (sig pt1)) → ⊥
rho-ne-act11 ()
-- act(2,3) 分离点: pt4
rho-ne-act12 : rho pt4 ≡ addE (mul2 pt4) (mul3 (sig pt4)) → ⊥
rho-ne-act12 ()
-- act(3,0) 分离点: pt2
rho-ne-act13 : rho pt2 ≡ addE (mul3 pt2) (act0 (sig pt2)) → ⊥
rho-ne-act13 ()
-- act(3,1) 分离点: pt1
rho-ne-act14 : rho pt1 ≡ addE (mul3 pt1) (act1 (sig pt1)) → ⊥
rho-ne-act14 ()
-- act(3,2) 分离点: pt2
rho-ne-act15 : rho pt2 ≡ addE (mul3 pt2) (mul2 (sig pt2)) → ⊥
rho-ne-act15 ()
-- act(3,3) 分离点: pt1
rho-ne-act16 : rho pt1 ≡ addE (mul3 pt1) (mul3 (sig pt1)) → ⊥
rho-ne-act16 ()

-- 分离见证 16 条（Z[σ]-作用映射去重 16 个全覆盖）
