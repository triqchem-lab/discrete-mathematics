{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.CurveF3
-- F₃ 上一般 Weierstrass 椭圆曲线：判别式与奇异性分类（M1 · A1.1 + A1.2）
--
-- 数学背景:
--   特征 3 下短形 y² = x³ + a·x + b 不可用——配平方消 x² 项需除以 3 ≡ 0，
--   故必须用一般形 E(a₂,a₄,a₆): y² = x³ + a₂x² + a₄x + a₆。
--   判别式: 通用式 Δ = b₂²b₄² − 4b₄³ − 4b₂³b₆ − 27b₆² + 18b₂b₄b₆ 在 mod 3 下
--   化为 Δ = a₂²a₄² + 2·a₄³ + 2·a₂³·a₆（−1 ≡ 2）。E 非奇异 ⟺ Δ ≢ 0。
--   F₃ 上 27 组参数中恰 **18 组非奇异**、9 组奇异（oracle 全枚举冻结，
--   两公式交叉验证一致；见 docs/plan/rh-allcurves-plan.md §一）。
--   迹/点计数不在本文件（A1.3/A1.4 的 CountF3.agda）；本文件只立曲线与分类。
--
-- 命名: 判别式函数定名 discF3 —— `disc` 已被 DiscreteKTheory.agda:573
--   （Witt 判别式）占用（AGENTS.md 查重前置）。
--
-- 本模块证明（0 postulate，全部 refl/λ()）:
--   §1 CurveF3 record + discF3
--   §2 27 组参数的逐组 Δ —— 与冻结表逐字一致（27 条 refl）
--   §3 奇异性分类 —— 18 条非奇异（IsNonSing 见证 λ()）+ 9 条奇异（refl）
--
-- 与旧件对照: BSD.agda 短形三条在本分类中为 E₁=c011(t=0)、E₂=c021(t=−3)、
--   E₆=c022(t=+3)（迹值由 A1.4 CountF3 给出）。

module Sovereign.Application.Problems.RH.CurveF3 where

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

--------------------------------------------------------------------------------
-- §1. record 与判别式
--------------------------------------------------------------------------------

record CurveF3 : Set where
  constructor mkC
  field
    a2 : Trit   -- x² 项系数（特征 3 下不可消去）
    a4 : Trit   -- x 项系数
    a6 : Trit   -- 常数项

-- Δ = a₂²a₄² + 2·a₄³ + 2·a₂³·a₆（mod 3；−1 ≡ 2，故两个负号写作 T₂ ⊗ …）
discF3 : CurveF3 → Trit
discF3 (mkC a₂ a₄ a₆) =
  (((a₂ ⊗ a₂) ⊗ (a₄ ⊗ a₄))
    ⊕ (T₂ ⊗ ((a₄ ⊗ a₄) ⊗ a₄)))
    ⊕ (T₂ ⊗ (((a₂ ⊗ a₂) ⊗ a₂) ⊗ a₆))

--------------------------------------------------------------------------------
-- §2. 27 组参数的逐组判别式（冻结表: docs/plan/rh-allcurves-plan.md §一）
--------------------------------------------------------------------------------

c000 c001 c002 c010 c011 c012 c020 c021 c022
  c100 c101 c102 c110 c111 c112 c120 c121 c122
  c200 c201 c202 c210 c211 c212 c220 c221 c222 : CurveF3
c000 = mkC T₀ T₀ T₀
c001 = mkC T₀ T₀ T₁
c002 = mkC T₀ T₀ T₂
c010 = mkC T₀ T₁ T₀
c011 = mkC T₀ T₁ T₁
c012 = mkC T₀ T₁ T₂
c020 = mkC T₀ T₂ T₀
c021 = mkC T₀ T₂ T₁
c022 = mkC T₀ T₂ T₂
c100 = mkC T₁ T₀ T₀
c101 = mkC T₁ T₀ T₁
c102 = mkC T₁ T₀ T₂
c110 = mkC T₁ T₁ T₀
c111 = mkC T₁ T₁ T₁
c112 = mkC T₁ T₁ T₂
c120 = mkC T₁ T₂ T₀
c121 = mkC T₁ T₂ T₁
c122 = mkC T₁ T₂ T₂
c200 = mkC T₂ T₀ T₀
c201 = mkC T₂ T₀ T₁
c202 = mkC T₂ T₀ T₂
c210 = mkC T₂ T₁ T₀
c211 = mkC T₂ T₁ T₁
c212 = mkC T₂ T₁ T₂
c220 = mkC T₂ T₂ T₀
c221 = mkC T₂ T₂ T₁
c222 = mkC T₂ T₂ T₂

-- 9 条奇异（Δ ≡ T₀）
disc-c000 : discF3 c000 ≡ T₀
disc-c000 = refl
disc-c001 : discF3 c001 ≡ T₀
disc-c001 = refl
disc-c002 : discF3 c002 ≡ T₀
disc-c002 = refl
disc-c100 : discF3 c100 ≡ T₀
disc-c100 = refl
disc-c110 : discF3 c110 ≡ T₀
disc-c110 = refl
disc-c122 : discF3 c122 ≡ T₀
disc-c122 = refl
disc-c200 : discF3 c200 ≡ T₀
disc-c200 = refl
disc-c210 : discF3 c210 ≡ T₀
disc-c210 = refl
disc-c221 : discF3 c221 ≡ T₀
disc-c221 = refl

-- 19 条非奇异的 Δ 值（分类见 §3；此处先给 27 全表的其余 18 条 + 1 条冗余核对）
disc-c010 : discF3 c010 ≡ T₂
disc-c010 = refl
disc-c011 : discF3 c011 ≡ T₂
disc-c011 = refl
disc-c012 : discF3 c012 ≡ T₂
disc-c012 = refl
disc-c020 : discF3 c020 ≡ T₁
disc-c020 = refl
disc-c021 : discF3 c021 ≡ T₁
disc-c021 = refl
disc-c022 : discF3 c022 ≡ T₁
disc-c022 = refl
disc-c101 : discF3 c101 ≡ T₂
disc-c101 = refl
disc-c102 : discF3 c102 ≡ T₁
disc-c102 = refl
disc-c111 : discF3 c111 ≡ T₂
disc-c111 = refl
disc-c112 : discF3 c112 ≡ T₁
disc-c112 = refl
disc-c120 : discF3 c120 ≡ T₂
disc-c120 = refl
disc-c121 : discF3 c121 ≡ T₁
disc-c121 = refl
disc-c201 : discF3 c201 ≡ T₁
disc-c201 = refl
disc-c202 : discF3 c202 ≡ T₂
disc-c202 = refl
disc-c211 : discF3 c211 ≡ T₁
disc-c211 = refl
disc-c212 : discF3 c212 ≡ T₂
disc-c212 = refl
disc-c220 : discF3 c220 ≡ T₂
disc-c220 = refl
disc-c222 : discF3 c222 ≡ T₁
disc-c222 = refl

--------------------------------------------------------------------------------
-- §3. 奇异性分类: 18 非奇异 + 9 奇异（恰覆盖 27 组，无重叠）
--------------------------------------------------------------------------------

IsNonSing : CurveF3 → Set
IsNonSing c = discF3 c ≢ T₀

-- 18 条非奇异见证（Δ ≡ T₁ 或 T₂ ⇒ “Δ ≡ T₀” 无构造子，λ() 吸收）
ns-c010 : IsNonSing c010
ns-c011 : IsNonSing c011
ns-c012 : IsNonSing c012
ns-c020 : IsNonSing c020
ns-c021 : IsNonSing c021
ns-c022 : IsNonSing c022
ns-c101 : IsNonSing c101
ns-c102 : IsNonSing c102
ns-c111 : IsNonSing c111
ns-c112 : IsNonSing c112
ns-c120 : IsNonSing c120
ns-c121 : IsNonSing c121
ns-c201 : IsNonSing c201
ns-c202 : IsNonSing c202
ns-c211 : IsNonSing c211
ns-c212 : IsNonSing c212
ns-c220 : IsNonSing c220
ns-c222 : IsNonSing c222
ns-c010 = λ ()
ns-c011 = λ ()
ns-c012 = λ ()
ns-c020 = λ ()
ns-c021 = λ ()
ns-c022 = λ ()
ns-c101 = λ ()
ns-c102 = λ ()
ns-c111 = λ ()
ns-c112 = λ ()
ns-c120 = λ ()
ns-c121 = λ ()
ns-c201 = λ ()
ns-c202 = λ ()
ns-c211 = λ ()
ns-c212 = λ ()
ns-c220 = λ ()
ns-c222 = λ ()

-- 9 条奇异（§2 已逐条 refl，此处以类型别名汇总备引）
IsSing : CurveF3 → Set
IsSing c = discF3 c ≡ T₀

sg-c000 : IsSing c000
sg-c001 : IsSing c001
sg-c002 : IsSing c002
sg-c100 : IsSing c100
sg-c110 : IsSing c110
sg-c122 : IsSing c122
sg-c200 : IsSing c200
sg-c210 : IsSing c210
sg-c221 : IsSing c221
sg-c000 = refl
sg-c001 = refl
sg-c002 = refl
sg-c100 = refl
sg-c110 = refl
sg-c122 = refl
sg-c200 = refl
sg-c210 = refl
sg-c221 = refl

--------------------------------------------------------------------------------
-- §4. 与旧件对照（BSD.agda 短形三条的位置；迹值见 CountF3，A1.3/A1.4）
--------------------------------------------------------------------------------

-- E₁ = y² = x³ + x + 1（c011）、E₂ = y² = x³ + 2x + 1（c021）、
-- E₆ = y² = x³ + 2x + 2（c022）——均非奇异（ns-c011/ns-c021/ns-c022）。
-- 本文件不重复定义迹；∀ Hasse（A1.5）将引用 A1.4 的迹表。
