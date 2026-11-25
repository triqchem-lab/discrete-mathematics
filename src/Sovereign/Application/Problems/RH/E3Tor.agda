{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.E3Tor
-- E[3](F₉) 破灭判据 = 超奇异的代数侧承载（M7 · E1-E3）
--
-- 数学背景（Deuring 代数侧的表驱动载体）:
--   超奇异 E/F₃ ⟺ E[3](F̄₃) 平凡（非 étale p-挠, Deuring）; 有限层:
--   E[3](F₉) = {P : mul3 P ≡ ptInf}。本件按 8 同构类逐类证得:
--   · 超奇异 4 类（cls0/5/6/7, t ∈ {0,±3}）: **e3-triv** —— mul3 p ≡ ptInf ⟹ p ≡ ptInf
--     （3-挠破灭; 非无穷点假设为空, () 拦截）
--   · 普通 4 类（cls1..4, t ∈ {±1,±2}）: **e3w** 非平凡 3-挠见证（每类恰 2 个 + ∞,
--     = C₃ 因子; 群阶 12/15 均含 3）—— oracle e3 模式全点枚举冻结（18 曲线 8 类逐类一致 ✓;
--     首版 mul3 从 P 起加误为 [4]P, 被判据交叉核对拦截修正）。
--   ⟹ 与 B4 的「p∣t」桥合流: 超奇异判据三表述（迹集/整除/E[3] 破灭）两两等价（逐类）。
--
-- 诚实边界:
--   · 这是 **F₉ 有理 3-挠**的破灭; 完整代数侧 E[3](F̄₃) = 0 需代闭点集（库内无;
--     B5 环论层同源, 未排期）。
--   · 全件独立具名引理形态（nightly 坑#5/#6 防患）; 表格 oracle e3/emit 逐字生成。
--   · 术语: 「超奇异」的「奇异」非几何奇点——分类域 18 条全部 disc ≢ 0（光滑）,
--     9 条 disc ≡ 0 奇异曲线在分类域外; 详见 docs/Riemann/挠结构与超奇异-术语注记。

module Sovereign.Application.Problems.RH.E3Tor where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Application.Problems.RH.CurveF3
open import Sovereign.Application.Problems.RH.CountF3
open import Sovereign.Application.Problems.RH.TraceTableF3
open import Sovereign.Application.Problems.RH.SupersingularF3
open import Sovereign.Application.Problems.RH.SupersingularDiv3
open import Sovereign.Application.Problems.RH.CurveIsoF3
import Sovereign.Application.Problems.RH.GroupCls0 as G0
import Sovereign.Application.Problems.RH.GroupCls1 as G1
import Sovereign.Application.Problems.RH.GroupCls2 as G2
import Sovereign.Application.Problems.RH.GroupCls3 as G3
import Sovereign.Application.Problems.RH.GroupCls4 as G4
import Sovereign.Application.Problems.RH.GroupCls5 as G5
import Sovereign.Application.Problems.RH.GroupCls6 as G6
import Sovereign.Application.Problems.RH.GroupCls7 as G7

--------------------------------------------------------------------------------
-- §1. 普通类非超奇异见证（sup-div3V + Div3V=⊥ 退化）
--------------------------------------------------------------------------------

notsup-c101 : IsSup c101 → ⊥
notsup-c101 s = sup-div3V c101 ns-c101 trM2 refl s  -- tℤ c101 ≡ val trM2, Div3V trM2 = ⊥

notsup-c102 : IsSup c102 → ⊥
notsup-c102 s = sup-div3V c102 ns-c102 trP1 refl s  -- tℤ c102 ≡ val trP1, Div3V trP1 = ⊥

notsup-c201 : IsSup c201 → ⊥
notsup-c201 s = sup-div3V c201 ns-c201 trM1 refl s  -- tℤ c201 ≡ val trM1, Div3V trM1 = ⊥

notsup-c202 : IsSup c202 → ⊥
notsup-c202 s = sup-div3V c202 ns-c202 trP2 refl s  -- tℤ c202 ≡ val trP2, Div3V trP2 = ⊥

--------------------------------------------------------------------------------
-- §2. 超奇异 4 类: e3-triv（3-挠破灭; mul3 表 oracle e3 逐字冻结）
--------------------------------------------------------------------------------

-- cls0（c010, t=+0; E(F₉) 16 点, 3-挠仅 ptInf）
e3-triv0 : ∀ p → G0.mul3 p ≡ G0.ptInf → p ≡ G0.ptInf
e3-triv0 G0.ptInf he = refl
e3-triv0 G0.pt1 ()  -- mul3 pt1 = pt1 ≠ ptInf
e3-triv0 G0.pt2 ()  -- mul3 pt2 = pt2 ≠ ptInf
e3-triv0 G0.pt3 ()  -- mul3 pt3 = pt3 ≠ ptInf
e3-triv0 G0.pt4 ()  -- mul3 pt4 = pt5 ≠ ptInf
e3-triv0 G0.pt5 ()  -- mul3 pt5 = pt4 ≠ ptInf
e3-triv0 G0.pt6 ()  -- mul3 pt6 = pt7 ≠ ptInf
e3-triv0 G0.pt7 ()  -- mul3 pt7 = pt6 ≠ ptInf
e3-triv0 G0.pt8 ()  -- mul3 pt8 = pt9 ≠ ptInf
e3-triv0 G0.pt9 ()  -- mul3 pt9 = pt8 ≠ ptInf
e3-triv0 G0.pt10 ()  -- mul3 pt10 = pt11 ≠ ptInf
e3-triv0 G0.pt11 ()  -- mul3 pt11 = pt10 ≠ ptInf
e3-triv0 G0.pt12 ()  -- mul3 pt12 = pt13 ≠ ptInf
e3-triv0 G0.pt13 ()  -- mul3 pt13 = pt12 ≠ ptInf
e3-triv0 G0.pt14 ()  -- mul3 pt14 = pt15 ≠ ptInf
e3-triv0 G0.pt15 ()  -- mul3 pt15 = pt14 ≠ ptInf

-- cls5（c020, t=+0; E(F₉) 16 点, 3-挠仅 ptInf）
e3-triv5 : ∀ p → G5.mul3 p ≡ G5.ptInf → p ≡ G5.ptInf
e3-triv5 G5.ptInf he = refl
e3-triv5 G5.pt1 ()  -- mul3 pt1 = pt1 ≠ ptInf
e3-triv5 G5.pt2 ()  -- mul3 pt2 = pt3 ≠ ptInf
e3-triv5 G5.pt3 ()  -- mul3 pt3 = pt2 ≠ ptInf
e3-triv5 G5.pt4 ()  -- mul3 pt4 = pt5 ≠ ptInf
e3-triv5 G5.pt5 ()  -- mul3 pt5 = pt4 ≠ ptInf
e3-triv5 G5.pt6 ()  -- mul3 pt6 = pt6 ≠ ptInf
e3-triv5 G5.pt7 ()  -- mul3 pt7 = pt8 ≠ ptInf
e3-triv5 G5.pt8 ()  -- mul3 pt8 = pt7 ≠ ptInf
e3-triv5 G5.pt9 ()  -- mul3 pt9 = pt10 ≠ ptInf
e3-triv5 G5.pt10 ()  -- mul3 pt10 = pt9 ≠ ptInf
e3-triv5 G5.pt11 ()  -- mul3 pt11 = pt11 ≠ ptInf
e3-triv5 G5.pt12 ()  -- mul3 pt12 = pt13 ≠ ptInf
e3-triv5 G5.pt13 ()  -- mul3 pt13 = pt12 ≠ ptInf
e3-triv5 G5.pt14 ()  -- mul3 pt14 = pt15 ≠ ptInf
e3-triv5 G5.pt15 ()  -- mul3 pt15 = pt14 ≠ ptInf

-- cls6（c021, t=-3; E(F₉) 7 点, 3-挠仅 ptInf）
e3-triv6 : ∀ p → G6.mul3 p ≡ G6.ptInf → p ≡ G6.ptInf
e3-triv6 G6.ptInf he = refl
e3-triv6 G6.pt1 ()  -- mul3 pt1 = pt6 ≠ ptInf
e3-triv6 G6.pt2 ()  -- mul3 pt2 = pt5 ≠ ptInf
e3-triv6 G6.pt3 ()  -- mul3 pt3 = pt2 ≠ ptInf
e3-triv6 G6.pt4 ()  -- mul3 pt4 = pt1 ≠ ptInf
e3-triv6 G6.pt5 ()  -- mul3 pt5 = pt4 ≠ ptInf
e3-triv6 G6.pt6 ()  -- mul3 pt6 = pt3 ≠ ptInf

-- cls7（c022, t=+3; E(F₉) 7 点, 3-挠仅 ptInf）
e3-triv7 : ∀ p → G7.mul3 p ≡ G7.ptInf → p ≡ G7.ptInf
e3-triv7 G7.ptInf he = refl
e3-triv7 G7.pt1 ()  -- mul3 pt1 = pt4 ≠ ptInf
e3-triv7 G7.pt2 ()  -- mul3 pt2 = pt3 ≠ ptInf
e3-triv7 G7.pt3 ()  -- mul3 pt3 = pt6 ≠ ptInf
e3-triv7 G7.pt4 ()  -- mul3 pt4 = pt5 ≠ ptInf
e3-triv7 G7.pt5 ()  -- mul3 pt5 = pt2 ≠ ptInf
e3-triv7 G7.pt6 ()  -- mul3 pt6 = pt1 ≠ ptInf

--------------------------------------------------------------------------------
-- §3. 普通 4 类: 非平凡 3-挠见证（每类恰 2 个; = C₃ 因子）
--------------------------------------------------------------------------------

-- cls1（c101, t=-2; E(F₉) 12 点, 3-挠 = {∞, pt8, pt9}）
e3w1-0 : G1.Pt1
e3w1-0 = G1.pt8
e3w-ne1-0 : e3w1-0 ≢ G1.ptInf
e3w-ne1-0 ()
e3w-tor1-0 : G1.mul3 e3w1-0 ≡ G1.ptInf
e3w-tor1-0 = refl
e3w1-1 : G1.Pt1
e3w1-1 = G1.pt9
e3w-ne1-1 : e3w1-1 ≢ G1.ptInf
e3w-ne1-1 ()
e3w-tor1-1 : G1.mul3 e3w1-1 ≡ G1.ptInf
e3w-tor1-1 = refl

-- cls2（c102, t=+1; E(F₉) 15 点, 3-挠 = {∞, pt3, pt4}）
e3w2-0 : G2.Pt2
e3w2-0 = G2.pt3
e3w-ne2-0 : e3w2-0 ≢ G2.ptInf
e3w-ne2-0 ()
e3w-tor2-0 : G2.mul3 e3w2-0 ≡ G2.ptInf
e3w-tor2-0 = refl
e3w2-1 : G2.Pt2
e3w2-1 = G2.pt4
e3w-ne2-1 : e3w2-1 ≢ G2.ptInf
e3w-ne2-1 ()
e3w-tor2-1 : G2.mul3 e3w2-1 ≡ G2.ptInf
e3w-tor2-1 = refl

-- cls3（c201, t=-1; E(F₉) 15 点, 3-挠 = {∞, pt9, pt10}）
e3w3-0 : G3.Pt3
e3w3-0 = G3.pt9
e3w-ne3-0 : e3w3-0 ≢ G3.ptInf
e3w-ne3-0 ()
e3w-tor3-0 : G3.mul3 e3w3-0 ≡ G3.ptInf
e3w-tor3-0 = refl
e3w3-1 : G3.Pt3
e3w3-1 = G3.pt10
e3w-ne3-1 : e3w3-1 ≢ G3.ptInf
e3w-ne3-1 ()
e3w-tor3-1 : G3.mul3 e3w3-1 ≡ G3.ptInf
e3w-tor3-1 = refl

-- cls4（c202, t=+2; E(F₉) 12 点, 3-挠 = {∞, pt7, pt8}）
e3w4-0 : G4.Pt4
e3w4-0 = G4.pt7
e3w-ne4-0 : e3w4-0 ≢ G4.ptInf
e3w-ne4-0 ()
e3w-tor4-0 : G4.mul3 e3w4-0 ≡ G4.ptInf
e3w-tor4-0 = refl
e3w4-1 : G4.Pt4
e3w4-1 = G4.pt8
e3w-ne4-1 : e3w4-1 ≢ G4.ptInf
e3w-ne4-1 ()
e3w-tor4-1 : G4.mul3 e3w4-1 ≡ G4.ptInf
e3w-tor4-1 = refl

--------------------------------------------------------------------------------
-- §4. 总桥（逐类）: IsSup (rep-of clsK) ↔ E[3] 破灭
--------------------------------------------------------------------------------

-- cls0: 超奇异 ✓（isSup-c010）+ e3-triv0 —— 两表述齐
-- cls5: 超奇异 ✓（isSup-c020）+ e3-triv5 —— 两表述齐
-- cls6: 超奇异 ✓（isSup-c021）+ e3-triv6 —— 两表述齐
-- cls7: 超奇异 ✓（isSup-c022）+ e3-triv7 —— 两表述齐

-- cls1: 非超奇异（notsup-c101）+ 非平凡 3-挠见证（e3w1-0/1）—— 两表述齐
-- cls2: 非超奇异（notsup-c102）+ 非平凡 3-挠见证（e3w2-0/1）—— 两表述齐
-- cls3: 非超奇异（notsup-c201）+ 非平凡 3-挠见证（e3w3-0/1）—— 两表述齐
-- cls4: 非超奇异（notsup-c202）+ 非平凡 3-挠见证（e3w4-0/1）—— 两表述齐

-- 三表述合流（逐类, 桥件）: 迹集式（water-iff）× 整除式（div3V-sup/sup-div3V）
-- × E[3] 破灭式（本件 e3-triv/e3w）——超奇异判据的表驱动完整承载
