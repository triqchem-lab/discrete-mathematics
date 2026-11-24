{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.CountF3
-- F₃ 一般 Weierstrass 曲线的点计数与迹表（M1 · A1.3 + A1.4）
--
-- 数学背景:
--   E(a₂,a₄,a₆): y² = x³ + a₂x² + a₄x + a₆（特征 3 下 x² 项不可消去）。
--   #E(F₃) = 1（无穷远点）+ Σ_{x∈F₃} #{y ∈ F₃ : y² = rhs(x)}。
--   y² = v 的解数 nsolY: v=T₀ → 1（y=T₀）；v=T₁ → 2（y=T₁,T₂，1²=2²=1）；
--   v=T₂ → 0（2 非平方）。迹 t = q + 1 − #E = 4 − #E（ℤ 层——负迹必须用 ℤ，
--   ℕ 的 _∸_ 会钳到 0；BSD.agda 的 ℕ 迹只对 #E ≤ 4 的曲线可用）。
--
-- 陈述冻结（oracle 全枚举，docs/plan/rh-allcurves-plan.md §一）:
--   18 条非奇异曲线的 (#E, t): c010(4,0) c011(4,0) c012(4,0) c020(4,0)
--   c021(7,−3) c022(1,+3) c101(6,−2) c102(3,+1) c111(6,−2) c112(3,+1)
--   c120(6,−2) c121(3,+1) c201(5,−1) c202(2,+2) c211(5,−1) c212(2,+2)
--   c220(2,+2) c222(5,−1)。迹集恰 7 值 {−3..3}。
--
-- 本模块证明（0 postulate，全部 refl）:
--   §1 nsolY / rhs / pointsE（一般形计数器）
--   §2 18 条非奇异曲线的 #E（与冻结表逐字一致）
--   §3 18 条曲线的 ℤ 迹（供 HasseAllF3 / WaterhouseF3 消费）
--
-- 交叉核对: c011 即 BSD.agda 的 E₁，pe-c011 : ≡ 4 与 #E1-is-4 一致；
--   c021/c022 即 E₂/E₆（#E 7/1 与 #E2-is-7 一致；E₆ 见 BSD §3）。

module Sovereign.Application.Problems.RH.CountF3 where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Integer using (ℤ; +_; -[1+_]; _-_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Application.Problems.RH.CurveF3

--------------------------------------------------------------------------------
-- §1. 计数器（一般形）
--------------------------------------------------------------------------------

-- rhs E x = x³ ⊕ a₂·x² ⊕ a₄·x ⊕ a₆
rhs : CurveF3 → Trit → Trit
rhs (mkC a₂ a₄ a₆) x =
  ((((x ⊗ x) ⊗ x) ⊕ (a₂ ⊗ (x ⊗ x))) ⊕ (a₄ ⊗ x)) ⊕ a₆

-- y² = v 的 F₃ 解数（直接计数, 无需平方表）
nsolY : Trit → ℕ
nsolY T₀ = 1
nsolY T₁ = 2
nsolY T₂ = 0

-- 单列: x 上曲线的仿射点数 = #{y : y² = rhs(x)}
colX : CurveF3 → Trit → ℕ
colX E x = nsolY (rhs E x)

-- #E(F₃) = 1（无穷远点）+ 三列之和
pointsE : CurveF3 → ℕ
pointsE E = suc (colX E T₀ + (colX E T₁ + colX E T₂))

-- ℤ 迹 t = 4 − #E
tℤ : CurveF3 → ℤ
tℤ E = + 4 - + (pointsE E)

--------------------------------------------------------------------------------
-- §2. 18 条非奇异曲线的 #E（与冻结表逐字一致）
--------------------------------------------------------------------------------

pe-c010 : pointsE c010 ≡ 4
pe-c010 = refl
pe-c011 : pointsE c011 ≡ 4
pe-c011 = refl
pe-c012 : pointsE c012 ≡ 4
pe-c012 = refl
pe-c020 : pointsE c020 ≡ 4
pe-c020 = refl
pe-c021 : pointsE c021 ≡ 7
pe-c021 = refl
pe-c022 : pointsE c022 ≡ 1
pe-c022 = refl
pe-c101 : pointsE c101 ≡ 6
pe-c101 = refl
pe-c102 : pointsE c102 ≡ 3
pe-c102 = refl
pe-c111 : pointsE c111 ≡ 6
pe-c111 = refl
pe-c112 : pointsE c112 ≡ 3
pe-c112 = refl
pe-c120 : pointsE c120 ≡ 6
pe-c120 = refl
pe-c121 : pointsE c121 ≡ 3
pe-c121 = refl
pe-c201 : pointsE c201 ≡ 5
pe-c201 = refl
pe-c202 : pointsE c202 ≡ 2
pe-c202 = refl
pe-c211 : pointsE c211 ≡ 5
pe-c211 = refl
pe-c212 : pointsE c212 ≡ 2
pe-c212 = refl
pe-c220 : pointsE c220 ≡ 2
pe-c220 = refl
pe-c222 : pointsE c222 ≡ 5
pe-c222 = refl

--------------------------------------------------------------------------------
-- §3. 18 条曲线的 ℤ 迹（§2 的转换; 冻结表 t 列）
--------------------------------------------------------------------------------

tr-c010 : tℤ c010 ≡ + 0
tr-c010 = refl
tr-c011 : tℤ c011 ≡ + 0
tr-c011 = refl
tr-c012 : tℤ c012 ≡ + 0
tr-c012 = refl
tr-c020 : tℤ c020 ≡ + 0
tr-c020 = refl
tr-c021 : tℤ c021 ≡ -[1+ 2 ]
tr-c021 = refl
tr-c022 : tℤ c022 ≡ + 3
tr-c022 = refl
tr-c101 : tℤ c101 ≡ -[1+ 1 ]
tr-c101 = refl
tr-c102 : tℤ c102 ≡ + 1
tr-c102 = refl
tr-c111 : tℤ c111 ≡ -[1+ 1 ]
tr-c111 = refl
tr-c112 : tℤ c112 ≡ + 1
tr-c112 = refl
tr-c120 : tℤ c120 ≡ -[1+ 1 ]
tr-c120 = refl
tr-c121 : tℤ c121 ≡ + 1
tr-c121 = refl
tr-c201 : tℤ c201 ≡ -[1+ 0 ]
tr-c201 = refl
tr-c202 : tℤ c202 ≡ + 2
tr-c202 = refl
tr-c211 : tℤ c211 ≡ -[1+ 0 ]
tr-c211 = refl
tr-c212 : tℤ c212 ≡ + 2
tr-c212 = refl
tr-c220 : tℤ c220 ≡ + 2
tr-c220 = refl
tr-c222 : tℤ c222 ≡ -[1+ 0 ]
tr-c222 = refl
