{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.EndRing5
-- M11·N5: ℤ[σ,ρ]-作用环核特征化（cls5 c020）—— 核三引理 + 商忠实性分离见证
--
-- 数学背景（oracle emit-ring 冻结, 先算后验; 256 候选 → 去重 64）:
--   · 作用映射 act(a,b,c,d) : p ↦ ([a]p + [b]·σp) + ([c]·ρp + [d]·σρp)
--   · **核 = 4 元**: (0,0,0,0) (0,0,2,2) (2,2,0,0) (2,2,2,2) —— actK* 三引理: 非平凡核元素逐点作用恒 ptInf
--   · **商忠实性**: 其余 63 个典范代表逐个有零分离点（act ≠ 零映射）
--     ⟹ 核 = 恰为「零作用元素」全体（64 元作用环的结构定案; 4096 合成全表不作——
--       合成封闭已 oracle 抽样冻结, Agda 承载取结构事实优先）
--
-- 诚实边界:
--   · 映射逐点等价层面; 「商环 ≅ Mat₂(ℤ/4) 的子环」的环同构表述不作
--   · 数值子句全部 oracle emit-ring 生成（先算后验纪律）

module Sovereign.Application.Problems.RH.EndRing5 where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Application.Problems.RH.GroupCls5
open import Sovereign.Application.Problems.RH.EndDistortion5

-- act0/act1 复用 EndDistortion（[0]=ptInf, [1]=id）

--------------------------------------------------------------------------------
-- §K. 核引理: 非平凡核元素逐点作用恒 ptInf
--------------------------------------------------------------------------------

-- 核元素 (0,0,2,2)
actK1 : Pt5 → Pt5
actK1 p = addE (addE (addE (act0 p) (act0 (sig p))) (mul2 (rho p))) (mul2 (sig (rho p)))
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

-- 核元素 (2,2,0,0)
actK2 : Pt5 → Pt5
actK2 p = addE (addE (addE (mul2 p) (mul2 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
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
actK3 : Pt5 → Pt5
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

act0000 : Pt5 → Pt5
act0000 p = addE (addE (addE (act0 p) (act0 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act0001 : Pt5 → Pt5
act0001 p = addE (addE (addE (act0 p) (act0 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act0002 : Pt5 → Pt5
act0002 p = addE (addE (addE (act0 p) (act0 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act0003 : Pt5 → Pt5
act0003 p = addE (addE (addE (act0 p) (act0 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act0010 : Pt5 → Pt5
act0010 p = addE (addE (addE (act0 p) (act0 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act0011 : Pt5 → Pt5
act0011 p = addE (addE (addE (act0 p) (act0 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act0012 : Pt5 → Pt5
act0012 p = addE (addE (addE (act0 p) (act0 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act0013 : Pt5 → Pt5
act0013 p = addE (addE (addE (act0 p) (act0 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))
act0100 : Pt5 → Pt5
act0100 p = addE (addE (addE (act0 p) (act1 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act0101 : Pt5 → Pt5
act0101 p = addE (addE (addE (act0 p) (act1 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act0102 : Pt5 → Pt5
act0102 p = addE (addE (addE (act0 p) (act1 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act0103 : Pt5 → Pt5
act0103 p = addE (addE (addE (act0 p) (act1 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act0110 : Pt5 → Pt5
act0110 p = addE (addE (addE (act0 p) (act1 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act0111 : Pt5 → Pt5
act0111 p = addE (addE (addE (act0 p) (act1 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act0112 : Pt5 → Pt5
act0112 p = addE (addE (addE (act0 p) (act1 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act0113 : Pt5 → Pt5
act0113 p = addE (addE (addE (act0 p) (act1 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))
act0200 : Pt5 → Pt5
act0200 p = addE (addE (addE (act0 p) (mul2 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act0201 : Pt5 → Pt5
act0201 p = addE (addE (addE (act0 p) (mul2 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act0202 : Pt5 → Pt5
act0202 p = addE (addE (addE (act0 p) (mul2 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act0203 : Pt5 → Pt5
act0203 p = addE (addE (addE (act0 p) (mul2 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act0210 : Pt5 → Pt5
act0210 p = addE (addE (addE (act0 p) (mul2 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act0211 : Pt5 → Pt5
act0211 p = addE (addE (addE (act0 p) (mul2 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act0212 : Pt5 → Pt5
act0212 p = addE (addE (addE (act0 p) (mul2 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act0213 : Pt5 → Pt5
act0213 p = addE (addE (addE (act0 p) (mul2 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))
act0300 : Pt5 → Pt5
act0300 p = addE (addE (addE (act0 p) (mul3 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act0301 : Pt5 → Pt5
act0301 p = addE (addE (addE (act0 p) (mul3 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act0302 : Pt5 → Pt5
act0302 p = addE (addE (addE (act0 p) (mul3 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act0303 : Pt5 → Pt5
act0303 p = addE (addE (addE (act0 p) (mul3 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act0310 : Pt5 → Pt5
act0310 p = addE (addE (addE (act0 p) (mul3 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act0311 : Pt5 → Pt5
act0311 p = addE (addE (addE (act0 p) (mul3 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act0312 : Pt5 → Pt5
act0312 p = addE (addE (addE (act0 p) (mul3 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act0313 : Pt5 → Pt5
act0313 p = addE (addE (addE (act0 p) (mul3 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))
act1000 : Pt5 → Pt5
act1000 p = addE (addE (addE (act1 p) (act0 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act1001 : Pt5 → Pt5
act1001 p = addE (addE (addE (act1 p) (act0 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act1002 : Pt5 → Pt5
act1002 p = addE (addE (addE (act1 p) (act0 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act1003 : Pt5 → Pt5
act1003 p = addE (addE (addE (act1 p) (act0 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act1010 : Pt5 → Pt5
act1010 p = addE (addE (addE (act1 p) (act0 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act1011 : Pt5 → Pt5
act1011 p = addE (addE (addE (act1 p) (act0 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act1012 : Pt5 → Pt5
act1012 p = addE (addE (addE (act1 p) (act0 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act1013 : Pt5 → Pt5
act1013 p = addE (addE (addE (act1 p) (act0 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))
act1100 : Pt5 → Pt5
act1100 p = addE (addE (addE (act1 p) (act1 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act1101 : Pt5 → Pt5
act1101 p = addE (addE (addE (act1 p) (act1 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act1102 : Pt5 → Pt5
act1102 p = addE (addE (addE (act1 p) (act1 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act1103 : Pt5 → Pt5
act1103 p = addE (addE (addE (act1 p) (act1 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act1110 : Pt5 → Pt5
act1110 p = addE (addE (addE (act1 p) (act1 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act1111 : Pt5 → Pt5
act1111 p = addE (addE (addE (act1 p) (act1 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act1112 : Pt5 → Pt5
act1112 p = addE (addE (addE (act1 p) (act1 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act1113 : Pt5 → Pt5
act1113 p = addE (addE (addE (act1 p) (act1 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))
act1200 : Pt5 → Pt5
act1200 p = addE (addE (addE (act1 p) (mul2 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act1201 : Pt5 → Pt5
act1201 p = addE (addE (addE (act1 p) (mul2 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act1202 : Pt5 → Pt5
act1202 p = addE (addE (addE (act1 p) (mul2 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act1203 : Pt5 → Pt5
act1203 p = addE (addE (addE (act1 p) (mul2 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act1210 : Pt5 → Pt5
act1210 p = addE (addE (addE (act1 p) (mul2 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act1211 : Pt5 → Pt5
act1211 p = addE (addE (addE (act1 p) (mul2 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act1212 : Pt5 → Pt5
act1212 p = addE (addE (addE (act1 p) (mul2 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act1213 : Pt5 → Pt5
act1213 p = addE (addE (addE (act1 p) (mul2 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))
act1300 : Pt5 → Pt5
act1300 p = addE (addE (addE (act1 p) (mul3 (sig p))) (act0 (rho p))) (act0 (sig (rho p)))
act1301 : Pt5 → Pt5
act1301 p = addE (addE (addE (act1 p) (mul3 (sig p))) (act0 (rho p))) (act1 (sig (rho p)))
act1302 : Pt5 → Pt5
act1302 p = addE (addE (addE (act1 p) (mul3 (sig p))) (act0 (rho p))) (mul2 (sig (rho p)))
act1303 : Pt5 → Pt5
act1303 p = addE (addE (addE (act1 p) (mul3 (sig p))) (act0 (rho p))) (mul3 (sig (rho p)))
act1310 : Pt5 → Pt5
act1310 p = addE (addE (addE (act1 p) (mul3 (sig p))) (act1 (rho p))) (act0 (sig (rho p)))
act1311 : Pt5 → Pt5
act1311 p = addE (addE (addE (act1 p) (mul3 (sig p))) (act1 (rho p))) (act1 (sig (rho p)))
act1312 : Pt5 → Pt5
act1312 p = addE (addE (addE (act1 p) (mul3 (sig p))) (act1 (rho p))) (mul2 (sig (rho p)))
act1313 : Pt5 → Pt5
act1313 p = addE (addE (addE (act1 p) (mul3 (sig p))) (act1 (rho p))) (mul3 (sig (rho p)))

--------------------------------------------------------------------------------
-- §S. ★ 商忠实性: 非零代表逐个有零分离点
--------------------------------------------------------------------------------

-- act(0,0,0,1) 分离点: pt1（作用值 pt1）
act0001-ne-zero : act0001 pt1 ≡ ptInf → ⊥
act0001-ne-zero ()
-- act(0,0,0,2) 分离点: pt2（作用值 pt1）
act0002-ne-zero : act0002 pt2 ≡ ptInf → ⊥
act0002-ne-zero ()
-- act(0,0,0,3) 分离点: pt1（作用值 pt1）
act0003-ne-zero : act0003 pt1 ≡ ptInf → ⊥
act0003-ne-zero ()
-- act(0,0,1,0) 分离点: pt1（作用值 pt1）
act0010-ne-zero : act0010 pt1 ≡ ptInf → ⊥
act0010-ne-zero ()
-- act(0,0,1,1) 分离点: pt2（作用值 pt6）
act0011-ne-zero : act0011 pt2 ≡ ptInf → ⊥
act0011-ne-zero ()
-- act(0,0,1,2) 分离点: pt1（作用值 pt1）
act0012-ne-zero : act0012 pt1 ≡ ptInf → ⊥
act0012-ne-zero ()
-- act(0,0,1,3) 分离点: pt2（作用值 pt11）
act0013-ne-zero : act0013 pt2 ≡ ptInf → ⊥
act0013-ne-zero ()
-- act(0,1,0,0) 分离点: pt1（作用值 pt1）
act0100-ne-zero : act0100 pt1 ≡ ptInf → ⊥
act0100-ne-zero ()
-- act(0,1,0,1) 分离点: pt2（作用值 pt6）
act0101-ne-zero : act0101 pt2 ≡ ptInf → ⊥
act0101-ne-zero ()
-- act(0,1,0,2) 分离点: pt1（作用值 pt1）
act0102-ne-zero : act0102 pt1 ≡ ptInf → ⊥
act0102-ne-zero ()
-- act(0,1,0,3) 分离点: pt2（作用值 pt11）
act0103-ne-zero : act0103 pt2 ≡ ptInf → ⊥
act0103-ne-zero ()
-- act(0,1,1,0) 分离点: pt2（作用值 pt1）
act0110-ne-zero : act0110 pt2 ≡ ptInf → ⊥
act0110-ne-zero ()
-- act(0,1,1,1) 分离点: pt1（作用值 pt1）
act0111-ne-zero : act0111 pt1 ≡ ptInf → ⊥
act0111-ne-zero ()
-- act(0,1,1,2) 分离点: pt4（作用值 pt1）
act0112-ne-zero : act0112 pt4 ≡ ptInf → ⊥
act0112-ne-zero ()
-- act(0,1,1,3) 分离点: pt1（作用值 pt1）
act0113-ne-zero : act0113 pt1 ≡ ptInf → ⊥
act0113-ne-zero ()
-- act(0,2,0,0) 分离点: pt2（作用值 pt1）
act0200-ne-zero : act0200 pt2 ≡ ptInf → ⊥
act0200-ne-zero ()
-- act(0,2,0,1) 分离点: pt1（作用值 pt1）
act0201-ne-zero : act0201 pt1 ≡ ptInf → ⊥
act0201-ne-zero ()
-- act(0,2,0,2) 分离点: pt7（作用值 pt1）
act0202-ne-zero : act0202 pt7 ≡ ptInf → ⊥
act0202-ne-zero ()
-- act(0,2,0,3) 分离点: pt1（作用值 pt1）
act0203-ne-zero : act0203 pt1 ≡ ptInf → ⊥
act0203-ne-zero ()
-- act(0,2,1,0) 分离点: pt1（作用值 pt1）
act0210-ne-zero : act0210 pt1 ≡ ptInf → ⊥
act0210-ne-zero ()
-- act(0,2,1,1) 分离点: pt2（作用值 pt11）
act0211-ne-zero : act0211 pt2 ≡ ptInf → ⊥
act0211-ne-zero ()
-- act(0,2,1,2) 分离点: pt1（作用值 pt1）
act0212-ne-zero : act0212 pt1 ≡ ptInf → ⊥
act0212-ne-zero ()
-- act(0,2,1,3) 分离点: pt2（作用值 pt6）
act0213-ne-zero : act0213 pt2 ≡ ptInf → ⊥
act0213-ne-zero ()
-- act(0,3,0,0) 分离点: pt1（作用值 pt1）
act0300-ne-zero : act0300 pt1 ≡ ptInf → ⊥
act0300-ne-zero ()
-- act(0,3,0,1) 分离点: pt2（作用值 pt11）
act0301-ne-zero : act0301 pt2 ≡ ptInf → ⊥
act0301-ne-zero ()
-- act(0,3,0,2) 分离点: pt1（作用值 pt1）
act0302-ne-zero : act0302 pt1 ≡ ptInf → ⊥
act0302-ne-zero ()
-- act(0,3,0,3) 分离点: pt2（作用值 pt6）
act0303-ne-zero : act0303 pt2 ≡ ptInf → ⊥
act0303-ne-zero ()
-- act(0,3,1,0) 分离点: pt4（作用值 pt1）
act0310-ne-zero : act0310 pt4 ≡ ptInf → ⊥
act0310-ne-zero ()
-- act(0,3,1,1) 分离点: pt1（作用值 pt1）
act0311-ne-zero : act0311 pt1 ≡ ptInf → ⊥
act0311-ne-zero ()
-- act(0,3,1,2) 分离点: pt2（作用值 pt1）
act0312-ne-zero : act0312 pt2 ≡ ptInf → ⊥
act0312-ne-zero ()
-- act(0,3,1,3) 分离点: pt1（作用值 pt1）
act0313-ne-zero : act0313 pt1 ≡ ptInf → ⊥
act0313-ne-zero ()
-- act(1,0,0,0) 分离点: pt1（作用值 pt1）
act1000-ne-zero : act1000 pt1 ≡ ptInf → ⊥
act1000-ne-zero ()
-- act(1,0,0,1) 分离点: pt2（作用值 pt1）
act1001-ne-zero : act1001 pt2 ≡ ptInf → ⊥
act1001-ne-zero ()
-- act(1,0,0,2) 分离点: pt1（作用值 pt1）
act1002-ne-zero : act1002 pt1 ≡ ptInf → ⊥
act1002-ne-zero ()
-- act(1,0,0,3) 分离点: pt4（作用值 pt1）
act1003-ne-zero : act1003 pt4 ≡ ptInf → ⊥
act1003-ne-zero ()
-- act(1,0,1,0) 分离点: pt2（作用值 pt6）
act1010-ne-zero : act1010 pt2 ≡ ptInf → ⊥
act1010-ne-zero ()
-- act(1,0,1,1) 分离点: pt1（作用值 pt1）
act1011-ne-zero : act1011 pt1 ≡ ptInf → ⊥
act1011-ne-zero ()
-- act(1,0,1,2) 分离点: pt2（作用值 pt11）
act1012-ne-zero : act1012 pt2 ≡ ptInf → ⊥
act1012-ne-zero ()
-- act(1,0,1,3) 分离点: pt1（作用值 pt1）
act1013-ne-zero : act1013 pt1 ≡ ptInf → ⊥
act1013-ne-zero ()
-- act(1,1,0,0) 分离点: pt2（作用值 pt6）
act1100-ne-zero : act1100 pt2 ≡ ptInf → ⊥
act1100-ne-zero ()
-- act(1,1,0,1) 分离点: pt1（作用值 pt1）
act1101-ne-zero : act1101 pt1 ≡ ptInf → ⊥
act1101-ne-zero ()
-- act(1,1,0,2) 分离点: pt2（作用值 pt11）
act1102-ne-zero : act1102 pt2 ≡ ptInf → ⊥
act1102-ne-zero ()
-- act(1,1,0,3) 分离点: pt1（作用值 pt1）
act1103-ne-zero : act1103 pt1 ≡ ptInf → ⊥
act1103-ne-zero ()
-- act(1,1,1,0) 分离点: pt1（作用值 pt1）
act1110-ne-zero : act1110 pt1 ≡ ptInf → ⊥
act1110-ne-zero ()
-- act(1,1,1,1) 分离点: pt7（作用值 pt6）
act1111-ne-zero : act1111 pt7 ≡ ptInf → ⊥
act1111-ne-zero ()
-- act(1,1,1,2) 分离点: pt1（作用值 pt1）
act1112-ne-zero : act1112 pt1 ≡ ptInf → ⊥
act1112-ne-zero ()
-- act(1,1,1,3) 分离点: pt2（作用值 pt1）
act1113-ne-zero : act1113 pt2 ≡ ptInf → ⊥
act1113-ne-zero ()
-- act(1,2,0,0) 分离点: pt1（作用值 pt1）
act1200-ne-zero : act1200 pt1 ≡ ptInf → ⊥
act1200-ne-zero ()
-- act(1,2,0,1) 分离点: pt4（作用值 pt1）
act1201-ne-zero : act1201 pt4 ≡ ptInf → ⊥
act1201-ne-zero ()
-- act(1,2,0,2) 分离点: pt1（作用值 pt1）
act1202-ne-zero : act1202 pt1 ≡ ptInf → ⊥
act1202-ne-zero ()
-- act(1,2,0,3) 分离点: pt2（作用值 pt1）
act1203-ne-zero : act1203 pt2 ≡ ptInf → ⊥
act1203-ne-zero ()
-- act(1,2,1,0) 分离点: pt2（作用值 pt11）
act1210-ne-zero : act1210 pt2 ≡ ptInf → ⊥
act1210-ne-zero ()
-- act(1,2,1,1) 分离点: pt1（作用值 pt1）
act1211-ne-zero : act1211 pt1 ≡ ptInf → ⊥
act1211-ne-zero ()
-- act(1,2,1,2) 分离点: pt2（作用值 pt6）
act1212-ne-zero : act1212 pt2 ≡ ptInf → ⊥
act1212-ne-zero ()
-- act(1,2,1,3) 分离点: pt1（作用值 pt1）
act1213-ne-zero : act1213 pt1 ≡ ptInf → ⊥
act1213-ne-zero ()
-- act(1,3,0,0) 分离点: pt2（作用值 pt11）
act1300-ne-zero : act1300 pt2 ≡ ptInf → ⊥
act1300-ne-zero ()
-- act(1,3,0,1) 分离点: pt1（作用值 pt1）
act1301-ne-zero : act1301 pt1 ≡ ptInf → ⊥
act1301-ne-zero ()
-- act(1,3,0,2) 分离点: pt2（作用值 pt6）
act1302-ne-zero : act1302 pt2 ≡ ptInf → ⊥
act1302-ne-zero ()
-- act(1,3,0,3) 分离点: pt1（作用值 pt1）
act1303-ne-zero : act1303 pt1 ≡ ptInf → ⊥
act1303-ne-zero ()
-- act(1,3,1,0) 分离点: pt1（作用值 pt1）
act1310-ne-zero : act1310 pt1 ≡ ptInf → ⊥
act1310-ne-zero ()
-- act(1,3,1,1) 分离点: pt2（作用值 pt1）
act1311-ne-zero : act1311 pt2 ≡ ptInf → ⊥
act1311-ne-zero ()
-- act(1,3,1,2) 分离点: pt1（作用值 pt1）
act1312-ne-zero : act1312 pt1 ≡ ptInf → ⊥
act1312-ne-zero ()
-- act(1,3,1,3) 分离点: pt7（作用值 pt11）
act1313-ne-zero : act1313 pt7 ≡ ptInf → ⊥
act1313-ne-zero ()

-- 核 4 元（actK3-zero ×3）+ 商忠实性分离 63 条 ——
-- 64 元作用环 = 256 候选 / 4 核; 核特征化完成
