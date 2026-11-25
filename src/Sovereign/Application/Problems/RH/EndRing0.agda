{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.EndRing0
-- M11·N5: ℤ[σ,ρ]-作用环核特征化（cls0 c010）—— 核三引理 + 商忠实性分离见证
--
-- 数学背景（oracle emit-ring 冻结, 先算后验; 256 候选 → 去重 64）:
--   · 作用映射 act(a,b,c,d) : p ↦ ([a]p + [b]·σp) + ([c]·ρp + [d]·σρp)
--   · **核 = 4 元**: (0,0,0,0) (0,2,2,0) (2,0,0,2) (2,2,2,2) —— actK* 三引理: 非平凡核元素逐点作用恒 ptInf
--   · **商忠实性**: 其余 63 个典范代表逐个有零分离点（act ≠ 零映射）
--     ⟹ 核 = 恰为「零作用元素」全体（64 元作用环的结构定案; 4096 合成全表不作——
--       合成封闭已 oracle 抽样冻结, Agda 承载取结构事实优先）
--
-- 诚实边界:
--   · 映射逐点等价层面; 「商环 ≅ Mat₂(ℤ/4) 的子环」的环同构表述不作
--   · 数值子句全部 oracle emit-ring 生成（先算后验纪律）

module Sovereign.Application.Problems.RH.EndRing0 where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Application.Problems.RH.GroupCls0
open import Sovereign.Application.Problems.RH.EndDistortion0

-- act0/act1 复用 EndDistortion（[0]=ptInf, [1]=id）

--------------------------------------------------------------------------------
-- §K. 核引理: 非平凡核元素逐点作用恒 ptInf
--------------------------------------------------------------------------------

-- 核元素 (0,2,2,0)
actK1 : Pt0 → Pt0
actK1 p = addE (addE (addE (act0 p) (mul2 (sig p))) (mul2 (rho p))) (act0 (sig (rho p)))
actK1-zero : ∀ p → actK1 p ≡ ptInf
actK1-zero ptInf = refl
actK1-zero pt1 = refl
actK1-zero pt2 = refl
actK1-zero pt3 = refl
actK1-zero pt4 = refl
actK1-zero pt5 = refl
actK1-zero pt6 = refl
actK1-zero pt7 = refl
actK1-zero pt8 = refl
actK1-zero pt9 = refl
actK1-zero pt10 = refl
actK1-zero pt11 = refl
actK1-zero pt12 = refl
actK1-zero pt13 = refl
actK1-zero pt14 = refl
actK1-zero pt15 = refl

-- 核元素 (2,0,0,2)
actK2 : Pt0 → Pt0
actK2 p = addE (addE (addE (mul2 p) (act0 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
actK2-zero : ∀ p → actK2 p ≡ ptInf
actK2-zero ptInf = refl
actK2-zero pt1 = refl
actK2-zero pt2 = refl
actK2-zero pt3 = refl
actK2-zero pt4 = refl
actK2-zero pt5 = refl
actK2-zero pt6 = refl
actK2-zero pt7 = refl
actK2-zero pt8 = refl
actK2-zero pt9 = refl
actK2-zero pt10 = refl
actK2-zero pt11 = refl
actK2-zero pt12 = refl
actK2-zero pt13 = refl
actK2-zero pt14 = refl
actK2-zero pt15 = refl

-- 核元素 (2,2,2,2)
actK3 : Pt0 → Pt0
actK3 p = addE (addE (addE (mul2 p) (mul2 (sig p))) (mul2 (rho p))) (mul2 (sig (rho p)))
actK3-zero : ∀ p → actK3 p ≡ ptInf
actK3-zero ptInf = refl
actK3-zero pt1 = refl
actK3-zero pt2 = refl
actK3-zero pt3 = refl
actK3-zero pt4 = refl
actK3-zero pt5 = refl
actK3-zero pt6 = refl
actK3-zero pt7 = refl
actK3-zero pt8 = refl
actK3-zero pt9 = refl
actK3-zero pt10 = refl
actK3-zero pt11 = refl
actK3-zero pt12 = refl
actK3-zero pt13 = refl
actK3-zero pt14 = refl
actK3-zero pt15 = refl

--------------------------------------------------------------------------------
-- §R. 作用环典范代表（去重 64; act00 = 零映射）
--------------------------------------------------------------------------------

act0000 : Pt0 → Pt0
act0000 p = addE (addE (addE (act0 p) (act0 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act0001 : Pt0 → Pt0
act0001 p = addE (addE (addE (act0 p) (act0 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act0002 : Pt0 → Pt0
act0002 p = addE (addE (addE (act0 p) (act0 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act0003 : Pt0 → Pt0
act0003 p = addE (addE (addE (act0 p) (act0 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act0010 : Pt0 → Pt0
act0010 p = addE (addE (addE (act0 p) (act0 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act0011 : Pt0 → Pt0
act0011 p = addE (addE (addE (act0 p) (act0 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act0012 : Pt0 → Pt0
act0012 p = addE (addE (addE (act0 p) (act0 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act0013 : Pt0 → Pt0
act0013 p = addE (addE (addE (act0 p) (act0 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))
act0020 : Pt0 → Pt0
act0020 p = addE (addE (addE (act0 p) (act0 (sig p))) (mul2 (rho p))) (act0 (sig (rho p)))
act0021 : Pt0 → Pt0
act0021 p = addE (addE (addE (act0 p) (act0 (sig p))) (mul2 (rho p))) (act1 (sig (rho p)))
act0022 : Pt0 → Pt0
act0022 p = addE (addE (addE (act0 p) (act0 (sig p))) (mul2 (rho p))) (mul2 (sig (rho p)))
act0023 : Pt0 → Pt0
act0023 p = addE (addE (addE (act0 p) (act0 (sig p))) (mul2 (rho p))) (mul3 (sig (rho p)))
act0030 : Pt0 → Pt0
act0030 p = addE (addE (addE (act0 p) (act0 (sig p))) (mul3 (rho p))) (act0 (sig (rho p)))
act0031 : Pt0 → Pt0
act0031 p = addE (addE (addE (act0 p) (act0 (sig p))) (mul3 (rho p))) (act1 (sig (rho p)))
act0032 : Pt0 → Pt0
act0032 p = addE (addE (addE (act0 p) (act0 (sig p))) (mul3 (rho p))) (mul2 (sig (rho p)))
act0033 : Pt0 → Pt0
act0033 p = addE (addE (addE (act0 p) (act0 (sig p))) (mul3 (rho p))) (mul3 (sig (rho p)))
act0100 : Pt0 → Pt0
act0100 p = addE (addE (addE (act0 p) (act1 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act0101 : Pt0 → Pt0
act0101 p = addE (addE (addE (act0 p) (act1 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act0102 : Pt0 → Pt0
act0102 p = addE (addE (addE (act0 p) (act1 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act0103 : Pt0 → Pt0
act0103 p = addE (addE (addE (act0 p) (act1 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act0110 : Pt0 → Pt0
act0110 p = addE (addE (addE (act0 p) (act1 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act0111 : Pt0 → Pt0
act0111 p = addE (addE (addE (act0 p) (act1 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act0112 : Pt0 → Pt0
act0112 p = addE (addE (addE (act0 p) (act1 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act0113 : Pt0 → Pt0
act0113 p = addE (addE (addE (act0 p) (act1 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))
act0120 : Pt0 → Pt0
act0120 p = addE (addE (addE (act0 p) (act1 (sig p))) (mul2 (rho p))) (act0 (sig (rho p)))
act0121 : Pt0 → Pt0
act0121 p = addE (addE (addE (act0 p) (act1 (sig p))) (mul2 (rho p))) (act1 (sig (rho p)))
act0122 : Pt0 → Pt0
act0122 p = addE (addE (addE (act0 p) (act1 (sig p))) (mul2 (rho p))) (mul2 (sig (rho p)))
act0123 : Pt0 → Pt0
act0123 p = addE (addE (addE (act0 p) (act1 (sig p))) (mul2 (rho p))) (mul3 (sig (rho p)))
act0130 : Pt0 → Pt0
act0130 p = addE (addE (addE (act0 p) (act1 (sig p))) (mul3 (rho p))) (act0 (sig (rho p)))
act0131 : Pt0 → Pt0
act0131 p = addE (addE (addE (act0 p) (act1 (sig p))) (mul3 (rho p))) (act1 (sig (rho p)))
act0132 : Pt0 → Pt0
act0132 p = addE (addE (addE (act0 p) (act1 (sig p))) (mul3 (rho p))) (mul2 (sig (rho p)))
act0133 : Pt0 → Pt0
act0133 p = addE (addE (addE (act0 p) (act1 (sig p))) (mul3 (rho p))) (mul3 (sig (rho p)))
act1000 : Pt0 → Pt0
act1000 p = addE (addE (addE (act1 p) (act0 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act1001 : Pt0 → Pt0
act1001 p = addE (addE (addE (act1 p) (act0 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act1002 : Pt0 → Pt0
act1002 p = addE (addE (addE (act1 p) (act0 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act1003 : Pt0 → Pt0
act1003 p = addE (addE (addE (act1 p) (act0 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act1010 : Pt0 → Pt0
act1010 p = addE (addE (addE (act1 p) (act0 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act1011 : Pt0 → Pt0
act1011 p = addE (addE (addE (act1 p) (act0 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act1012 : Pt0 → Pt0
act1012 p = addE (addE (addE (act1 p) (act0 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act1013 : Pt0 → Pt0
act1013 p = addE (addE (addE (act1 p) (act0 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))
act1020 : Pt0 → Pt0
act1020 p = addE (addE (addE (act1 p) (act0 (sig p))) (mul2 (rho p))) (act0 (sig (rho p)))
act1021 : Pt0 → Pt0
act1021 p = addE (addE (addE (act1 p) (act0 (sig p))) (mul2 (rho p))) (act1 (sig (rho p)))
act1022 : Pt0 → Pt0
act1022 p = addE (addE (addE (act1 p) (act0 (sig p))) (mul2 (rho p))) (mul2 (sig (rho p)))
act1023 : Pt0 → Pt0
act1023 p = addE (addE (addE (act1 p) (act0 (sig p))) (mul2 (rho p))) (mul3 (sig (rho p)))
act1030 : Pt0 → Pt0
act1030 p = addE (addE (addE (act1 p) (act0 (sig p))) (mul3 (rho p))) (act0 (sig (rho p)))
act1031 : Pt0 → Pt0
act1031 p = addE (addE (addE (act1 p) (act0 (sig p))) (mul3 (rho p))) (act1 (sig (rho p)))
act1032 : Pt0 → Pt0
act1032 p = addE (addE (addE (act1 p) (act0 (sig p))) (mul3 (rho p))) (mul2 (sig (rho p)))
act1033 : Pt0 → Pt0
act1033 p = addE (addE (addE (act1 p) (act0 (sig p))) (mul3 (rho p))) (mul3 (sig (rho p)))
act1100 : Pt0 → Pt0
act1100 p = addE (addE (addE (act1 p) (act1 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act1101 : Pt0 → Pt0
act1101 p = addE (addE (addE (act1 p) (act1 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act1102 : Pt0 → Pt0
act1102 p = addE (addE (addE (act1 p) (act1 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act1103 : Pt0 → Pt0
act1103 p = addE (addE (addE (act1 p) (act1 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act1110 : Pt0 → Pt0
act1110 p = addE (addE (addE (act1 p) (act1 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act1111 : Pt0 → Pt0
act1111 p = addE (addE (addE (act1 p) (act1 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act1112 : Pt0 → Pt0
act1112 p = addE (addE (addE (act1 p) (act1 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act1113 : Pt0 → Pt0
act1113 p = addE (addE (addE (act1 p) (act1 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))
act1120 : Pt0 → Pt0
act1120 p = addE (addE (addE (act1 p) (act1 (sig p))) (mul2 (rho p))) (act0 (sig (rho p)))
act1121 : Pt0 → Pt0
act1121 p = addE (addE (addE (act1 p) (act1 (sig p))) (mul2 (rho p))) (act1 (sig (rho p)))
act1122 : Pt0 → Pt0
act1122 p = addE (addE (addE (act1 p) (act1 (sig p))) (mul2 (rho p))) (mul2 (sig (rho p)))
act1123 : Pt0 → Pt0
act1123 p = addE (addE (addE (act1 p) (act1 (sig p))) (mul2 (rho p))) (mul3 (sig (rho p)))
act1130 : Pt0 → Pt0
act1130 p = addE (addE (addE (act1 p) (act1 (sig p))) (mul3 (rho p))) (act0 (sig (rho p)))
act1131 : Pt0 → Pt0
act1131 p = addE (addE (addE (act1 p) (act1 (sig p))) (mul3 (rho p))) (act1 (sig (rho p)))
act1132 : Pt0 → Pt0
act1132 p = addE (addE (addE (act1 p) (act1 (sig p))) (mul3 (rho p))) (mul2 (sig (rho p)))
act1133 : Pt0 → Pt0
act1133 p = addE (addE (addE (act1 p) (act1 (sig p))) (mul3 (rho p))) (mul3 (sig (rho p)))

--------------------------------------------------------------------------------
-- §S. ★ 商忠实性: 非零代表逐个有零分离点
--------------------------------------------------------------------------------

-- act(0,0,0,1) 分离点: pt1（作用值 pt1）
act0001-ne-zero : act0001 pt1 ≡ ptInf → ⊥
act0001-ne-zero ()
-- act(0,0,0,2) 分离点: pt4（作用值 pt1）
act0002-ne-zero : act0002 pt4 ≡ ptInf → ⊥
act0002-ne-zero ()
-- act(0,0,0,3) 分离点: pt1（作用值 pt1）
act0003-ne-zero : act0003 pt1 ≡ ptInf → ⊥
act0003-ne-zero ()
-- act(0,0,1,0) 分离点: pt1（作用值 pt1）
act0010-ne-zero : act0010 pt1 ≡ ptInf → ⊥
act0010-ne-zero ()
-- act(0,0,1,1) 分离点: pt2（作用值 pt1）
act0011-ne-zero : act0011 pt2 ≡ ptInf → ⊥
act0011-ne-zero ()
-- act(0,0,1,2) 分离点: pt1（作用值 pt1）
act0012-ne-zero : act0012 pt1 ≡ ptInf → ⊥
act0012-ne-zero ()
-- act(0,0,1,3) 分离点: pt2（作用值 pt1）
act0013-ne-zero : act0013 pt2 ≡ ptInf → ⊥
act0013-ne-zero ()
-- act(0,0,2,0) 分离点: pt4（作用值 pt1）
act0020-ne-zero : act0020 pt4 ≡ ptInf → ⊥
act0020-ne-zero ()
-- act(0,0,2,1) 分离点: pt1（作用值 pt1）
act0021-ne-zero : act0021 pt1 ≡ ptInf → ⊥
act0021-ne-zero ()
-- act(0,0,2,2) 分离点: pt6（作用值 pt1）
act0022-ne-zero : act0022 pt6 ≡ ptInf → ⊥
act0022-ne-zero ()
-- act(0,0,2,3) 分离点: pt1（作用值 pt1）
act0023-ne-zero : act0023 pt1 ≡ ptInf → ⊥
act0023-ne-zero ()
-- act(0,0,3,0) 分离点: pt1（作用值 pt1）
act0030-ne-zero : act0030 pt1 ≡ ptInf → ⊥
act0030-ne-zero ()
-- act(0,0,3,1) 分离点: pt2（作用值 pt1）
act0031-ne-zero : act0031 pt2 ≡ ptInf → ⊥
act0031-ne-zero ()
-- act(0,0,3,2) 分离点: pt1（作用值 pt1）
act0032-ne-zero : act0032 pt1 ≡ ptInf → ⊥
act0032-ne-zero ()
-- act(0,0,3,3) 分离点: pt2（作用值 pt1）
act0033-ne-zero : act0033 pt2 ≡ ptInf → ⊥
act0033-ne-zero ()
-- act(0,1,0,0) 分离点: pt1（作用值 pt1）
act0100-ne-zero : act0100 pt1 ≡ ptInf → ⊥
act0100-ne-zero ()
-- act(0,1,0,1) 分离点: pt2（作用值 pt1）
act0101-ne-zero : act0101 pt2 ≡ ptInf → ⊥
act0101-ne-zero ()
-- act(0,1,0,2) 分离点: pt1（作用值 pt1）
act0102-ne-zero : act0102 pt1 ≡ ptInf → ⊥
act0102-ne-zero ()
-- act(0,1,0,3) 分离点: pt2（作用值 pt1）
act0103-ne-zero : act0103 pt2 ≡ ptInf → ⊥
act0103-ne-zero ()
-- act(0,1,1,0) 分离点: pt4（作用值 pt2）
act0110-ne-zero : act0110 pt4 ≡ ptInf → ⊥
act0110-ne-zero ()
-- act(0,1,1,1) 分离点: pt1（作用值 pt1）
act0111-ne-zero : act0111 pt1 ≡ ptInf → ⊥
act0111-ne-zero ()
-- act(0,1,1,2) 分离点: pt4（作用值 pt3）
act0112-ne-zero : act0112 pt4 ≡ ptInf → ⊥
act0112-ne-zero ()
-- act(0,1,1,3) 分离点: pt1（作用值 pt1）
act0113-ne-zero : act0113 pt1 ≡ ptInf → ⊥
act0113-ne-zero ()
-- act(0,1,2,0) 分离点: pt1（作用值 pt1）
act0120-ne-zero : act0120 pt1 ≡ ptInf → ⊥
act0120-ne-zero ()
-- act(0,1,2,1) 分离点: pt2（作用值 pt1）
act0121-ne-zero : act0121 pt2 ≡ ptInf → ⊥
act0121-ne-zero ()
-- act(0,1,2,2) 分离点: pt1（作用值 pt1）
act0122-ne-zero : act0122 pt1 ≡ ptInf → ⊥
act0122-ne-zero ()
-- act(0,1,2,3) 分离点: pt2（作用值 pt1）
act0123-ne-zero : act0123 pt2 ≡ ptInf → ⊥
act0123-ne-zero ()
-- act(0,1,3,0) 分离点: pt4（作用值 pt3）
act0130-ne-zero : act0130 pt4 ≡ ptInf → ⊥
act0130-ne-zero ()
-- act(0,1,3,1) 分离点: pt1（作用值 pt1）
act0131-ne-zero : act0131 pt1 ≡ ptInf → ⊥
act0131-ne-zero ()
-- act(0,1,3,2) 分离点: pt4（作用值 pt2）
act0132-ne-zero : act0132 pt4 ≡ ptInf → ⊥
act0132-ne-zero ()
-- act(0,1,3,3) 分离点: pt1（作用值 pt1）
act0133-ne-zero : act0133 pt1 ≡ ptInf → ⊥
act0133-ne-zero ()
-- act(1,0,0,0) 分离点: pt1（作用值 pt1）
act1000-ne-zero : act1000 pt1 ≡ ptInf → ⊥
act1000-ne-zero ()
-- act(1,0,0,1) 分离点: pt4（作用值 pt3）
act1001-ne-zero : act1001 pt4 ≡ ptInf → ⊥
act1001-ne-zero ()
-- act(1,0,0,2) 分离点: pt1（作用值 pt1）
act1002-ne-zero : act1002 pt1 ≡ ptInf → ⊥
act1002-ne-zero ()
-- act(1,0,0,3) 分离点: pt4（作用值 pt2）
act1003-ne-zero : act1003 pt4 ≡ ptInf → ⊥
act1003-ne-zero ()
-- act(1,0,1,0) 分离点: pt2（作用值 pt1）
act1010-ne-zero : act1010 pt2 ≡ ptInf → ⊥
act1010-ne-zero ()
-- act(1,0,1,1) 分离点: pt1（作用值 pt1）
act1011-ne-zero : act1011 pt1 ≡ ptInf → ⊥
act1011-ne-zero ()
-- act(1,0,1,2) 分离点: pt2（作用值 pt1）
act1012-ne-zero : act1012 pt2 ≡ ptInf → ⊥
act1012-ne-zero ()
-- act(1,0,1,3) 分离点: pt1（作用值 pt1）
act1013-ne-zero : act1013 pt1 ≡ ptInf → ⊥
act1013-ne-zero ()
-- act(1,0,2,0) 分离点: pt1（作用值 pt1）
act1020-ne-zero : act1020 pt1 ≡ ptInf → ⊥
act1020-ne-zero ()
-- act(1,0,2,1) 分离点: pt4（作用值 pt2）
act1021-ne-zero : act1021 pt4 ≡ ptInf → ⊥
act1021-ne-zero ()
-- act(1,0,2,2) 分离点: pt1（作用值 pt1）
act1022-ne-zero : act1022 pt1 ≡ ptInf → ⊥
act1022-ne-zero ()
-- act(1,0,2,3) 分离点: pt4（作用值 pt3）
act1023-ne-zero : act1023 pt4 ≡ ptInf → ⊥
act1023-ne-zero ()
-- act(1,0,3,0) 分离点: pt2（作用值 pt1）
act1030-ne-zero : act1030 pt2 ≡ ptInf → ⊥
act1030-ne-zero ()
-- act(1,0,3,1) 分离点: pt1（作用值 pt1）
act1031-ne-zero : act1031 pt1 ≡ ptInf → ⊥
act1031-ne-zero ()
-- act(1,0,3,2) 分离点: pt2（作用值 pt1）
act1032-ne-zero : act1032 pt2 ≡ ptInf → ⊥
act1032-ne-zero ()
-- act(1,0,3,3) 分离点: pt1（作用值 pt1）
act1033-ne-zero : act1033 pt1 ≡ ptInf → ⊥
act1033-ne-zero ()
-- act(1,1,0,0) 分离点: pt2（作用值 pt1）
act1100-ne-zero : act1100 pt2 ≡ ptInf → ⊥
act1100-ne-zero ()
-- act(1,1,0,1) 分离点: pt1（作用值 pt1）
act1101-ne-zero : act1101 pt1 ≡ ptInf → ⊥
act1101-ne-zero ()
-- act(1,1,0,2) 分离点: pt2（作用值 pt1）
act1102-ne-zero : act1102 pt2 ≡ ptInf → ⊥
act1102-ne-zero ()
-- act(1,1,0,3) 分离点: pt1（作用值 pt1）
act1103-ne-zero : act1103 pt1 ≡ ptInf → ⊥
act1103-ne-zero ()
-- act(1,1,1,0) 分离点: pt1（作用值 pt1）
act1110-ne-zero : act1110 pt1 ≡ ptInf → ⊥
act1110-ne-zero ()
-- act(1,1,1,1) 分离点: pt4（作用值 pt1）
act1111-ne-zero : act1111 pt4 ≡ ptInf → ⊥
act1111-ne-zero ()
-- act(1,1,1,2) 分离点: pt1（作用值 pt1）
act1112-ne-zero : act1112 pt1 ≡ ptInf → ⊥
act1112-ne-zero ()
-- act(1,1,1,3) 分离点: pt6（作用值 pt2）
act1113-ne-zero : act1113 pt6 ≡ ptInf → ⊥
act1113-ne-zero ()
-- act(1,1,2,0) 分离点: pt2（作用值 pt1）
act1120-ne-zero : act1120 pt2 ≡ ptInf → ⊥
act1120-ne-zero ()
-- act(1,1,2,1) 分离点: pt1（作用值 pt1）
act1121-ne-zero : act1121 pt1 ≡ ptInf → ⊥
act1121-ne-zero ()
-- act(1,1,2,2) 分离点: pt2（作用值 pt1）
act1122-ne-zero : act1122 pt2 ≡ ptInf → ⊥
act1122-ne-zero ()
-- act(1,1,2,3) 分离点: pt1（作用值 pt1）
act1123-ne-zero : act1123 pt1 ≡ ptInf → ⊥
act1123-ne-zero ()
-- act(1,1,3,0) 分离点: pt1（作用值 pt1）
act1130-ne-zero : act1130 pt1 ≡ ptInf → ⊥
act1130-ne-zero ()
-- act(1,1,3,1) 分离点: pt6（作用值 pt3）
act1131-ne-zero : act1131 pt6 ≡ ptInf → ⊥
act1131-ne-zero ()
-- act(1,1,3,2) 分离点: pt1（作用值 pt1）
act1132-ne-zero : act1132 pt1 ≡ ptInf → ⊥
act1132-ne-zero ()
-- act(1,1,3,3) 分离点: pt4（作用值 pt1）
act1133-ne-zero : act1133 pt4 ≡ ptInf → ⊥
act1133-ne-zero ()

-- 核 4 元（actK3-zero ×3）+ 商忠实性分离 63 条 ——
-- 64 元作用环 = 256 候选 / 4 核; 核特征化完成
