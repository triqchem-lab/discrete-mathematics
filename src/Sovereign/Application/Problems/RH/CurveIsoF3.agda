{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.CurveIsoF3
-- F₃ 同构分类: 18 条非奇异曲线的 x-平移轨道 = 恰 8 类（M3 续 · A5.2①）
--
-- 数学背景:
--   特征 3 内我们形（a₁=a₃=0）的可行同构: x → x + r（r ∈ F₃）与 y → ±y（对 y² 平凡）;
--   u-缩放 x → u²x, y → u³y 在 mod 3 下平凡（u⁴ ≡ u⁶ ≡ 1）。
--   平移作用: a₂ 不变（(x+r)³ ≡ x³ + r³）; a₄ → 2a₂r + a₄; a₆ → r³ + a₂r² + a₄r + a₆。
--   **18 条非奇异 → 恰 8 个平移轨道**（oracle emit-iso 冻结; 与经典「F₃ 上恰 8 个
--   椭圆曲线同构类」计数一致 [未形式化·经典对照]）。
--   cls0..cls7 代表元: c010/c101/c102/c201/c202/c020/c021/c022。
--   轨道表（oracle iso 模式, 迹逐轨一致 ✓）:
--     cls0 [c010 c011 c012] t=0 | cls1 [c101 c111 c120] t=−2 | cls2 [c102 c112 c121] t=+1
--     cls3 [c201 c211 c222] t=−1 | cls4 [c202 c212 c220] t=+2
--     cls5 [c020] t=0 | cls6 [c021] t=−3 | cls7 [c022] t=+3
--   交叉核对: disc/#E 平移不变性 27×3 oracle ✓ + Agda ds/ps 162 条; 每轨道迹一致
--   oracle ✓ + Agda ct 18 条。
--
-- 诚实边界:
--   · 「恰 8 类」的完全陈述 = 覆盖（cls-of 18 分派）+ 非空（rep-of/ns-rep 8 见证）+
--     互斥（ne-cls* 28 条）+ 轨道封闭（sic 54 条）——四件齐;
--     「平移是全部同构」的逆命题（任何形内同构都是平移±y）未形式化 [直觉·未验证]。
--   · 奇异 9 条不在分类域内（cls-of 分派时假设真用 ⊥-elim）。
--   · 本件全部数值子句由 oracle emit-iso 逐字生成（先算后验纪律）。
--   · 【nightly 坑#5】全件用**独立具名引理**形态: 分派子句块（∀ 函数 + 多子句）之前
--     若悬置其他已声明未定义的签名, 子句 refl 检查会被污染（CannotApply/UnequalTerms,
--     2026-11-25 M1-M4 二分实证）——唯 cls-of 因被 sic 引用必须保持函数形态,
--     其签名与子句块之间零间隔。

module Sovereign.Application.Problems.RH.CurveIsoF3 where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Application.Problems.RH.CurveF3
open import Sovereign.Application.Problems.RH.CountF3

--------------------------------------------------------------------------------
-- §1. 平移作用（char 3 展开: (x+r)³ ≡ x³ + r³; 乘法字面量先行 —— 具体 r 下全归约）
--------------------------------------------------------------------------------

xshift : CurveF3 → Trit → CurveF3
xshift (mkC a₂ a₄ a₆) r =
  mkC a₂
      (((T₂ ⊗ r) ⊗ a₂) ⊕ a₄)
      ((((r ⊗ r) ⊗ r) ⊕ ((r ⊗ r) ⊗ a₂)) ⊕ ((r ⊗ a₄) ⊕ a₆))

--------------------------------------------------------------------------------
-- §2. 类型层: 8 个平移轨道
--------------------------------------------------------------------------------

data Cls3 : Set where
  cls0 cls1 cls2 cls3 cls4 cls5 cls6 cls7 : Cls3

-- 代表元（cls0..cls7 ↦ c010/c101/c102/c201/c202/c020/c021/c022）
rep-of : Cls3 → CurveF3
rep-of cls0 = c010
rep-of cls1 = c101
rep-of cls2 = c102
rep-of cls3 = c201
rep-of cls4 = c202
rep-of cls5 = c020
rep-of cls6 = c021
rep-of cls7 = c022

ns-rep : ∀ (w : Cls3) → IsNonSing (rep-of w)
ns-rep cls0 = ns-c010
ns-rep cls1 = ns-c101
ns-rep cls2 = ns-c102
ns-rep cls3 = ns-c201
ns-rep cls4 = ns-c202
ns-rep cls5 = ns-c020
ns-rep cls6 = ns-c021
ns-rep cls7 = ns-c022

-- 分类函数（18 非奇异分派 + 9 奇异假设真用; 签名与子句零间隔, 见坑#5）
cls-of : ∀ (c : CurveF3) → IsNonSing c → Cls3

--------------------------------------------------------------------------------
-- §3. disc-shift 独立引理 81 条（oracle emit-iso 逐字）
--------------------------------------------------------------------------------

ds-c000-T₀ : discF3 (xshift c000 T₀) ≡ discF3 c000
ds-c000-T₀ = refl
ds-c000-T₁ : discF3 (xshift c000 T₁) ≡ discF3 c000
ds-c000-T₁ = refl
ds-c000-T₂ : discF3 (xshift c000 T₂) ≡ discF3 c000
ds-c000-T₂ = refl
ds-c001-T₀ : discF3 (xshift c001 T₀) ≡ discF3 c001
ds-c001-T₀ = refl
ds-c001-T₁ : discF3 (xshift c001 T₁) ≡ discF3 c001
ds-c001-T₁ = refl
ds-c001-T₂ : discF3 (xshift c001 T₂) ≡ discF3 c001
ds-c001-T₂ = refl
ds-c002-T₀ : discF3 (xshift c002 T₀) ≡ discF3 c002
ds-c002-T₀ = refl
ds-c002-T₁ : discF3 (xshift c002 T₁) ≡ discF3 c002
ds-c002-T₁ = refl
ds-c002-T₂ : discF3 (xshift c002 T₂) ≡ discF3 c002
ds-c002-T₂ = refl
ds-c010-T₀ : discF3 (xshift c010 T₀) ≡ discF3 c010
ds-c010-T₀ = refl
ds-c010-T₁ : discF3 (xshift c010 T₁) ≡ discF3 c010
ds-c010-T₁ = refl
ds-c010-T₂ : discF3 (xshift c010 T₂) ≡ discF3 c010
ds-c010-T₂ = refl
ds-c011-T₀ : discF3 (xshift c011 T₀) ≡ discF3 c011
ds-c011-T₀ = refl
ds-c011-T₁ : discF3 (xshift c011 T₁) ≡ discF3 c011
ds-c011-T₁ = refl
ds-c011-T₂ : discF3 (xshift c011 T₂) ≡ discF3 c011
ds-c011-T₂ = refl
ds-c012-T₀ : discF3 (xshift c012 T₀) ≡ discF3 c012
ds-c012-T₀ = refl
ds-c012-T₁ : discF3 (xshift c012 T₁) ≡ discF3 c012
ds-c012-T₁ = refl
ds-c012-T₂ : discF3 (xshift c012 T₂) ≡ discF3 c012
ds-c012-T₂ = refl
ds-c020-T₀ : discF3 (xshift c020 T₀) ≡ discF3 c020
ds-c020-T₀ = refl
ds-c020-T₁ : discF3 (xshift c020 T₁) ≡ discF3 c020
ds-c020-T₁ = refl
ds-c020-T₂ : discF3 (xshift c020 T₂) ≡ discF3 c020
ds-c020-T₂ = refl
ds-c021-T₀ : discF3 (xshift c021 T₀) ≡ discF3 c021
ds-c021-T₀ = refl
ds-c021-T₁ : discF3 (xshift c021 T₁) ≡ discF3 c021
ds-c021-T₁ = refl
ds-c021-T₂ : discF3 (xshift c021 T₂) ≡ discF3 c021
ds-c021-T₂ = refl
ds-c022-T₀ : discF3 (xshift c022 T₀) ≡ discF3 c022
ds-c022-T₀ = refl
ds-c022-T₁ : discF3 (xshift c022 T₁) ≡ discF3 c022
ds-c022-T₁ = refl
ds-c022-T₂ : discF3 (xshift c022 T₂) ≡ discF3 c022
ds-c022-T₂ = refl
ds-c100-T₀ : discF3 (xshift c100 T₀) ≡ discF3 c100
ds-c100-T₀ = refl
ds-c100-T₁ : discF3 (xshift c100 T₁) ≡ discF3 c100
ds-c100-T₁ = refl
ds-c100-T₂ : discF3 (xshift c100 T₂) ≡ discF3 c100
ds-c100-T₂ = refl
ds-c101-T₀ : discF3 (xshift c101 T₀) ≡ discF3 c101
ds-c101-T₀ = refl
ds-c101-T₁ : discF3 (xshift c101 T₁) ≡ discF3 c101
ds-c101-T₁ = refl
ds-c101-T₂ : discF3 (xshift c101 T₂) ≡ discF3 c101
ds-c101-T₂ = refl
ds-c102-T₀ : discF3 (xshift c102 T₀) ≡ discF3 c102
ds-c102-T₀ = refl
ds-c102-T₁ : discF3 (xshift c102 T₁) ≡ discF3 c102
ds-c102-T₁ = refl
ds-c102-T₂ : discF3 (xshift c102 T₂) ≡ discF3 c102
ds-c102-T₂ = refl
ds-c110-T₀ : discF3 (xshift c110 T₀) ≡ discF3 c110
ds-c110-T₀ = refl
ds-c110-T₁ : discF3 (xshift c110 T₁) ≡ discF3 c110
ds-c110-T₁ = refl
ds-c110-T₂ : discF3 (xshift c110 T₂) ≡ discF3 c110
ds-c110-T₂ = refl
ds-c111-T₀ : discF3 (xshift c111 T₀) ≡ discF3 c111
ds-c111-T₀ = refl
ds-c111-T₁ : discF3 (xshift c111 T₁) ≡ discF3 c111
ds-c111-T₁ = refl
ds-c111-T₂ : discF3 (xshift c111 T₂) ≡ discF3 c111
ds-c111-T₂ = refl
ds-c112-T₀ : discF3 (xshift c112 T₀) ≡ discF3 c112
ds-c112-T₀ = refl
ds-c112-T₁ : discF3 (xshift c112 T₁) ≡ discF3 c112
ds-c112-T₁ = refl
ds-c112-T₂ : discF3 (xshift c112 T₂) ≡ discF3 c112
ds-c112-T₂ = refl
ds-c120-T₀ : discF3 (xshift c120 T₀) ≡ discF3 c120
ds-c120-T₀ = refl
ds-c120-T₁ : discF3 (xshift c120 T₁) ≡ discF3 c120
ds-c120-T₁ = refl
ds-c120-T₂ : discF3 (xshift c120 T₂) ≡ discF3 c120
ds-c120-T₂ = refl
ds-c121-T₀ : discF3 (xshift c121 T₀) ≡ discF3 c121
ds-c121-T₀ = refl
ds-c121-T₁ : discF3 (xshift c121 T₁) ≡ discF3 c121
ds-c121-T₁ = refl
ds-c121-T₂ : discF3 (xshift c121 T₂) ≡ discF3 c121
ds-c121-T₂ = refl
ds-c122-T₀ : discF3 (xshift c122 T₀) ≡ discF3 c122
ds-c122-T₀ = refl
ds-c122-T₁ : discF3 (xshift c122 T₁) ≡ discF3 c122
ds-c122-T₁ = refl
ds-c122-T₂ : discF3 (xshift c122 T₂) ≡ discF3 c122
ds-c122-T₂ = refl
ds-c200-T₀ : discF3 (xshift c200 T₀) ≡ discF3 c200
ds-c200-T₀ = refl
ds-c200-T₁ : discF3 (xshift c200 T₁) ≡ discF3 c200
ds-c200-T₁ = refl
ds-c200-T₂ : discF3 (xshift c200 T₂) ≡ discF3 c200
ds-c200-T₂ = refl
ds-c201-T₀ : discF3 (xshift c201 T₀) ≡ discF3 c201
ds-c201-T₀ = refl
ds-c201-T₁ : discF3 (xshift c201 T₁) ≡ discF3 c201
ds-c201-T₁ = refl
ds-c201-T₂ : discF3 (xshift c201 T₂) ≡ discF3 c201
ds-c201-T₂ = refl
ds-c202-T₀ : discF3 (xshift c202 T₀) ≡ discF3 c202
ds-c202-T₀ = refl
ds-c202-T₁ : discF3 (xshift c202 T₁) ≡ discF3 c202
ds-c202-T₁ = refl
ds-c202-T₂ : discF3 (xshift c202 T₂) ≡ discF3 c202
ds-c202-T₂ = refl
ds-c210-T₀ : discF3 (xshift c210 T₀) ≡ discF3 c210
ds-c210-T₀ = refl
ds-c210-T₁ : discF3 (xshift c210 T₁) ≡ discF3 c210
ds-c210-T₁ = refl
ds-c210-T₂ : discF3 (xshift c210 T₂) ≡ discF3 c210
ds-c210-T₂ = refl
ds-c211-T₀ : discF3 (xshift c211 T₀) ≡ discF3 c211
ds-c211-T₀ = refl
ds-c211-T₁ : discF3 (xshift c211 T₁) ≡ discF3 c211
ds-c211-T₁ = refl
ds-c211-T₂ : discF3 (xshift c211 T₂) ≡ discF3 c211
ds-c211-T₂ = refl
ds-c212-T₀ : discF3 (xshift c212 T₀) ≡ discF3 c212
ds-c212-T₀ = refl
ds-c212-T₁ : discF3 (xshift c212 T₁) ≡ discF3 c212
ds-c212-T₁ = refl
ds-c212-T₂ : discF3 (xshift c212 T₂) ≡ discF3 c212
ds-c212-T₂ = refl
ds-c220-T₀ : discF3 (xshift c220 T₀) ≡ discF3 c220
ds-c220-T₀ = refl
ds-c220-T₁ : discF3 (xshift c220 T₁) ≡ discF3 c220
ds-c220-T₁ = refl
ds-c220-T₂ : discF3 (xshift c220 T₂) ≡ discF3 c220
ds-c220-T₂ = refl
ds-c221-T₀ : discF3 (xshift c221 T₀) ≡ discF3 c221
ds-c221-T₀ = refl
ds-c221-T₁ : discF3 (xshift c221 T₁) ≡ discF3 c221
ds-c221-T₁ = refl
ds-c221-T₂ : discF3 (xshift c221 T₂) ≡ discF3 c221
ds-c221-T₂ = refl
ds-c222-T₀ : discF3 (xshift c222 T₀) ≡ discF3 c222
ds-c222-T₀ = refl
ds-c222-T₁ : discF3 (xshift c222 T₁) ≡ discF3 c222
ds-c222-T₁ = refl
ds-c222-T₂ : discF3 (xshift c222 T₂) ≡ discF3 c222
ds-c222-T₂ = refl

--------------------------------------------------------------------------------
-- §4. pts-shift 独立引理 81 条（oracle emit-iso 逐字）
--------------------------------------------------------------------------------

ps-c000-T₀ : pointsE (xshift c000 T₀) ≡ pointsE c000
ps-c000-T₀ = refl
ps-c000-T₁ : pointsE (xshift c000 T₁) ≡ pointsE c000
ps-c000-T₁ = refl
ps-c000-T₂ : pointsE (xshift c000 T₂) ≡ pointsE c000
ps-c000-T₂ = refl
ps-c001-T₀ : pointsE (xshift c001 T₀) ≡ pointsE c001
ps-c001-T₀ = refl
ps-c001-T₁ : pointsE (xshift c001 T₁) ≡ pointsE c001
ps-c001-T₁ = refl
ps-c001-T₂ : pointsE (xshift c001 T₂) ≡ pointsE c001
ps-c001-T₂ = refl
ps-c002-T₀ : pointsE (xshift c002 T₀) ≡ pointsE c002
ps-c002-T₀ = refl
ps-c002-T₁ : pointsE (xshift c002 T₁) ≡ pointsE c002
ps-c002-T₁ = refl
ps-c002-T₂ : pointsE (xshift c002 T₂) ≡ pointsE c002
ps-c002-T₂ = refl
ps-c010-T₀ : pointsE (xshift c010 T₀) ≡ pointsE c010
ps-c010-T₀ = refl
ps-c010-T₁ : pointsE (xshift c010 T₁) ≡ pointsE c010
ps-c010-T₁ = refl
ps-c010-T₂ : pointsE (xshift c010 T₂) ≡ pointsE c010
ps-c010-T₂ = refl
ps-c011-T₀ : pointsE (xshift c011 T₀) ≡ pointsE c011
ps-c011-T₀ = refl
ps-c011-T₁ : pointsE (xshift c011 T₁) ≡ pointsE c011
ps-c011-T₁ = refl
ps-c011-T₂ : pointsE (xshift c011 T₂) ≡ pointsE c011
ps-c011-T₂ = refl
ps-c012-T₀ : pointsE (xshift c012 T₀) ≡ pointsE c012
ps-c012-T₀ = refl
ps-c012-T₁ : pointsE (xshift c012 T₁) ≡ pointsE c012
ps-c012-T₁ = refl
ps-c012-T₂ : pointsE (xshift c012 T₂) ≡ pointsE c012
ps-c012-T₂ = refl
ps-c020-T₀ : pointsE (xshift c020 T₀) ≡ pointsE c020
ps-c020-T₀ = refl
ps-c020-T₁ : pointsE (xshift c020 T₁) ≡ pointsE c020
ps-c020-T₁ = refl
ps-c020-T₂ : pointsE (xshift c020 T₂) ≡ pointsE c020
ps-c020-T₂ = refl
ps-c021-T₀ : pointsE (xshift c021 T₀) ≡ pointsE c021
ps-c021-T₀ = refl
ps-c021-T₁ : pointsE (xshift c021 T₁) ≡ pointsE c021
ps-c021-T₁ = refl
ps-c021-T₂ : pointsE (xshift c021 T₂) ≡ pointsE c021
ps-c021-T₂ = refl
ps-c022-T₀ : pointsE (xshift c022 T₀) ≡ pointsE c022
ps-c022-T₀ = refl
ps-c022-T₁ : pointsE (xshift c022 T₁) ≡ pointsE c022
ps-c022-T₁ = refl
ps-c022-T₂ : pointsE (xshift c022 T₂) ≡ pointsE c022
ps-c022-T₂ = refl
ps-c100-T₀ : pointsE (xshift c100 T₀) ≡ pointsE c100
ps-c100-T₀ = refl
ps-c100-T₁ : pointsE (xshift c100 T₁) ≡ pointsE c100
ps-c100-T₁ = refl
ps-c100-T₂ : pointsE (xshift c100 T₂) ≡ pointsE c100
ps-c100-T₂ = refl
ps-c101-T₀ : pointsE (xshift c101 T₀) ≡ pointsE c101
ps-c101-T₀ = refl
ps-c101-T₁ : pointsE (xshift c101 T₁) ≡ pointsE c101
ps-c101-T₁ = refl
ps-c101-T₂ : pointsE (xshift c101 T₂) ≡ pointsE c101
ps-c101-T₂ = refl
ps-c102-T₀ : pointsE (xshift c102 T₀) ≡ pointsE c102
ps-c102-T₀ = refl
ps-c102-T₁ : pointsE (xshift c102 T₁) ≡ pointsE c102
ps-c102-T₁ = refl
ps-c102-T₂ : pointsE (xshift c102 T₂) ≡ pointsE c102
ps-c102-T₂ = refl
ps-c110-T₀ : pointsE (xshift c110 T₀) ≡ pointsE c110
ps-c110-T₀ = refl
ps-c110-T₁ : pointsE (xshift c110 T₁) ≡ pointsE c110
ps-c110-T₁ = refl
ps-c110-T₂ : pointsE (xshift c110 T₂) ≡ pointsE c110
ps-c110-T₂ = refl
ps-c111-T₀ : pointsE (xshift c111 T₀) ≡ pointsE c111
ps-c111-T₀ = refl
ps-c111-T₁ : pointsE (xshift c111 T₁) ≡ pointsE c111
ps-c111-T₁ = refl
ps-c111-T₂ : pointsE (xshift c111 T₂) ≡ pointsE c111
ps-c111-T₂ = refl
ps-c112-T₀ : pointsE (xshift c112 T₀) ≡ pointsE c112
ps-c112-T₀ = refl
ps-c112-T₁ : pointsE (xshift c112 T₁) ≡ pointsE c112
ps-c112-T₁ = refl
ps-c112-T₂ : pointsE (xshift c112 T₂) ≡ pointsE c112
ps-c112-T₂ = refl
ps-c120-T₀ : pointsE (xshift c120 T₀) ≡ pointsE c120
ps-c120-T₀ = refl
ps-c120-T₁ : pointsE (xshift c120 T₁) ≡ pointsE c120
ps-c120-T₁ = refl
ps-c120-T₂ : pointsE (xshift c120 T₂) ≡ pointsE c120
ps-c120-T₂ = refl
ps-c121-T₀ : pointsE (xshift c121 T₀) ≡ pointsE c121
ps-c121-T₀ = refl
ps-c121-T₁ : pointsE (xshift c121 T₁) ≡ pointsE c121
ps-c121-T₁ = refl
ps-c121-T₂ : pointsE (xshift c121 T₂) ≡ pointsE c121
ps-c121-T₂ = refl
ps-c122-T₀ : pointsE (xshift c122 T₀) ≡ pointsE c122
ps-c122-T₀ = refl
ps-c122-T₁ : pointsE (xshift c122 T₁) ≡ pointsE c122
ps-c122-T₁ = refl
ps-c122-T₂ : pointsE (xshift c122 T₂) ≡ pointsE c122
ps-c122-T₂ = refl
ps-c200-T₀ : pointsE (xshift c200 T₀) ≡ pointsE c200
ps-c200-T₀ = refl
ps-c200-T₁ : pointsE (xshift c200 T₁) ≡ pointsE c200
ps-c200-T₁ = refl
ps-c200-T₂ : pointsE (xshift c200 T₂) ≡ pointsE c200
ps-c200-T₂ = refl
ps-c201-T₀ : pointsE (xshift c201 T₀) ≡ pointsE c201
ps-c201-T₀ = refl
ps-c201-T₁ : pointsE (xshift c201 T₁) ≡ pointsE c201
ps-c201-T₁ = refl
ps-c201-T₂ : pointsE (xshift c201 T₂) ≡ pointsE c201
ps-c201-T₂ = refl
ps-c202-T₀ : pointsE (xshift c202 T₀) ≡ pointsE c202
ps-c202-T₀ = refl
ps-c202-T₁ : pointsE (xshift c202 T₁) ≡ pointsE c202
ps-c202-T₁ = refl
ps-c202-T₂ : pointsE (xshift c202 T₂) ≡ pointsE c202
ps-c202-T₂ = refl
ps-c210-T₀ : pointsE (xshift c210 T₀) ≡ pointsE c210
ps-c210-T₀ = refl
ps-c210-T₁ : pointsE (xshift c210 T₁) ≡ pointsE c210
ps-c210-T₁ = refl
ps-c210-T₂ : pointsE (xshift c210 T₂) ≡ pointsE c210
ps-c210-T₂ = refl
ps-c211-T₀ : pointsE (xshift c211 T₀) ≡ pointsE c211
ps-c211-T₀ = refl
ps-c211-T₁ : pointsE (xshift c211 T₁) ≡ pointsE c211
ps-c211-T₁ = refl
ps-c211-T₂ : pointsE (xshift c211 T₂) ≡ pointsE c211
ps-c211-T₂ = refl
ps-c212-T₀ : pointsE (xshift c212 T₀) ≡ pointsE c212
ps-c212-T₀ = refl
ps-c212-T₁ : pointsE (xshift c212 T₁) ≡ pointsE c212
ps-c212-T₁ = refl
ps-c212-T₂ : pointsE (xshift c212 T₂) ≡ pointsE c212
ps-c212-T₂ = refl
ps-c220-T₀ : pointsE (xshift c220 T₀) ≡ pointsE c220
ps-c220-T₀ = refl
ps-c220-T₁ : pointsE (xshift c220 T₁) ≡ pointsE c220
ps-c220-T₁ = refl
ps-c220-T₂ : pointsE (xshift c220 T₂) ≡ pointsE c220
ps-c220-T₂ = refl
ps-c221-T₀ : pointsE (xshift c221 T₀) ≡ pointsE c221
ps-c221-T₀ = refl
ps-c221-T₁ : pointsE (xshift c221 T₁) ≡ pointsE c221
ps-c221-T₁ = refl
ps-c221-T₂ : pointsE (xshift c221 T₂) ≡ pointsE c221
ps-c221-T₂ = refl
ps-c222-T₀ : pointsE (xshift c222 T₀) ≡ pointsE c222
ps-c222-T₀ = refl
ps-c222-T₁ : pointsE (xshift c222 T₁) ≡ pointsE c222
ps-c222-T₁ = refl
ps-c222-T₂ : pointsE (xshift c222 T₂) ≡ pointsE c222
ps-c222-T₂ = refl

--------------------------------------------------------------------------------
-- §2c. cls-of 27 条（oracle emit-iso 逐字）
--------------------------------------------------------------------------------

cls-of (mkC T₀ T₀ T₀) h = ⊥-elim (h refl)
cls-of (mkC T₀ T₀ T₁) h = ⊥-elim (h refl)
cls-of (mkC T₀ T₀ T₂) h = ⊥-elim (h refl)
cls-of (mkC T₀ T₁ T₀) h = cls0
cls-of (mkC T₀ T₁ T₁) h = cls0
cls-of (mkC T₀ T₁ T₂) h = cls0
cls-of (mkC T₀ T₂ T₀) h = cls5
cls-of (mkC T₀ T₂ T₁) h = cls6
cls-of (mkC T₀ T₂ T₂) h = cls7
cls-of (mkC T₁ T₀ T₀) h = ⊥-elim (h refl)
cls-of (mkC T₁ T₀ T₁) h = cls1
cls-of (mkC T₁ T₀ T₂) h = cls2
cls-of (mkC T₁ T₁ T₀) h = ⊥-elim (h refl)
cls-of (mkC T₁ T₁ T₁) h = cls1
cls-of (mkC T₁ T₁ T₂) h = cls2
cls-of (mkC T₁ T₂ T₀) h = cls1
cls-of (mkC T₁ T₂ T₁) h = cls2
cls-of (mkC T₁ T₂ T₂) h = ⊥-elim (h refl)
cls-of (mkC T₂ T₀ T₀) h = ⊥-elim (h refl)
cls-of (mkC T₂ T₀ T₁) h = cls3
cls-of (mkC T₂ T₀ T₂) h = cls4
cls-of (mkC T₂ T₁ T₀) h = ⊥-elim (h refl)
cls-of (mkC T₂ T₁ T₁) h = cls3
cls-of (mkC T₂ T₁ T₂) h = cls4
cls-of (mkC T₂ T₂ T₀) h = cls4
cls-of (mkC T₂ T₂ T₁) h = ⊥-elim (h refl)
cls-of (mkC T₂ T₂ T₂) h = cls3


--------------------------------------------------------------------------------
-- §2d. ns-ds 54 条
--------------------------------------------------------------------------------

ns-ds-c010-0 : IsNonSing c010
ns-ds-c010-0 = ns-c010
ns-ds-c010-1 : IsNonSing c012
ns-ds-c010-1 = ns-c012
ns-ds-c010-2 : IsNonSing c011
ns-ds-c010-2 = ns-c011
ns-ds-c011-0 : IsNonSing c011
ns-ds-c011-0 = ns-c011
ns-ds-c011-1 : IsNonSing c010
ns-ds-c011-1 = ns-c010
ns-ds-c011-2 : IsNonSing c012
ns-ds-c011-2 = ns-c012
ns-ds-c012-0 : IsNonSing c012
ns-ds-c012-0 = ns-c012
ns-ds-c012-1 : IsNonSing c011
ns-ds-c012-1 = ns-c011
ns-ds-c012-2 : IsNonSing c010
ns-ds-c012-2 = ns-c010
ns-ds-c020-0 : IsNonSing c020
ns-ds-c020-0 = ns-c020
ns-ds-c020-1 : IsNonSing c020
ns-ds-c020-1 = ns-c020
ns-ds-c020-2 : IsNonSing c020
ns-ds-c020-2 = ns-c020
ns-ds-c021-0 : IsNonSing c021
ns-ds-c021-0 = ns-c021
ns-ds-c021-1 : IsNonSing c021
ns-ds-c021-1 = ns-c021
ns-ds-c021-2 : IsNonSing c021
ns-ds-c021-2 = ns-c021
ns-ds-c022-0 : IsNonSing c022
ns-ds-c022-0 = ns-c022
ns-ds-c022-1 : IsNonSing c022
ns-ds-c022-1 = ns-c022
ns-ds-c022-2 : IsNonSing c022
ns-ds-c022-2 = ns-c022
ns-ds-c101-0 : IsNonSing c101
ns-ds-c101-0 = ns-c101
ns-ds-c101-1 : IsNonSing c120
ns-ds-c101-1 = ns-c120
ns-ds-c101-2 : IsNonSing c111
ns-ds-c101-2 = ns-c111
ns-ds-c102-0 : IsNonSing c102
ns-ds-c102-0 = ns-c102
ns-ds-c102-1 : IsNonSing c121
ns-ds-c102-1 = ns-c121
ns-ds-c102-2 : IsNonSing c112
ns-ds-c102-2 = ns-c112
ns-ds-c111-0 : IsNonSing c111
ns-ds-c111-0 = ns-c111
ns-ds-c111-1 : IsNonSing c101
ns-ds-c111-1 = ns-c101
ns-ds-c111-2 : IsNonSing c120
ns-ds-c111-2 = ns-c120
ns-ds-c112-0 : IsNonSing c112
ns-ds-c112-0 = ns-c112
ns-ds-c112-1 : IsNonSing c102
ns-ds-c112-1 = ns-c102
ns-ds-c112-2 : IsNonSing c121
ns-ds-c112-2 = ns-c121
ns-ds-c120-0 : IsNonSing c120
ns-ds-c120-0 = ns-c120
ns-ds-c120-1 : IsNonSing c111
ns-ds-c120-1 = ns-c111
ns-ds-c120-2 : IsNonSing c101
ns-ds-c120-2 = ns-c101
ns-ds-c121-0 : IsNonSing c121
ns-ds-c121-0 = ns-c121
ns-ds-c121-1 : IsNonSing c112
ns-ds-c121-1 = ns-c112
ns-ds-c121-2 : IsNonSing c102
ns-ds-c121-2 = ns-c102
ns-ds-c201-0 : IsNonSing c201
ns-ds-c201-0 = ns-c201
ns-ds-c201-1 : IsNonSing c211
ns-ds-c201-1 = ns-c211
ns-ds-c201-2 : IsNonSing c222
ns-ds-c201-2 = ns-c222
ns-ds-c202-0 : IsNonSing c202
ns-ds-c202-0 = ns-c202
ns-ds-c202-1 : IsNonSing c212
ns-ds-c202-1 = ns-c212
ns-ds-c202-2 : IsNonSing c220
ns-ds-c202-2 = ns-c220
ns-ds-c211-0 : IsNonSing c211
ns-ds-c211-0 = ns-c211
ns-ds-c211-1 : IsNonSing c222
ns-ds-c211-1 = ns-c222
ns-ds-c211-2 : IsNonSing c201
ns-ds-c211-2 = ns-c201
ns-ds-c212-0 : IsNonSing c212
ns-ds-c212-0 = ns-c212
ns-ds-c212-1 : IsNonSing c220
ns-ds-c212-1 = ns-c220
ns-ds-c212-2 : IsNonSing c202
ns-ds-c212-2 = ns-c202
ns-ds-c220-0 : IsNonSing c220
ns-ds-c220-0 = ns-c220
ns-ds-c220-1 : IsNonSing c202
ns-ds-c220-1 = ns-c202
ns-ds-c220-2 : IsNonSing c212
ns-ds-c220-2 = ns-c212
ns-ds-c222-0 : IsNonSing c222
ns-ds-c222-0 = ns-c222
ns-ds-c222-1 : IsNonSing c201
ns-ds-c222-1 = ns-c201
ns-ds-c222-2 : IsNonSing c211
ns-ds-c222-2 = ns-c211


--------------------------------------------------------------------------------
-- §2e. sic 54 条（轨道封闭; oracle emit-iso 逐字）
--------------------------------------------------------------------------------

sic-c010-0 : cls-of c010 ns-ds-c010-0 ≡ cls-of c010 ns-c010
sic-c010-0 = refl  -- c010 --r=0--> c010
sic-c010-1 : cls-of c012 ns-ds-c010-1 ≡ cls-of c010 ns-c010
sic-c010-1 = refl  -- c010 --r=1--> c012
sic-c010-2 : cls-of c011 ns-ds-c010-2 ≡ cls-of c010 ns-c010
sic-c010-2 = refl  -- c010 --r=2--> c011
sic-c011-0 : cls-of c011 ns-ds-c011-0 ≡ cls-of c011 ns-c011
sic-c011-0 = refl  -- c011 --r=0--> c011
sic-c011-1 : cls-of c010 ns-ds-c011-1 ≡ cls-of c011 ns-c011
sic-c011-1 = refl  -- c011 --r=1--> c010
sic-c011-2 : cls-of c012 ns-ds-c011-2 ≡ cls-of c011 ns-c011
sic-c011-2 = refl  -- c011 --r=2--> c012
sic-c012-0 : cls-of c012 ns-ds-c012-0 ≡ cls-of c012 ns-c012
sic-c012-0 = refl  -- c012 --r=0--> c012
sic-c012-1 : cls-of c011 ns-ds-c012-1 ≡ cls-of c012 ns-c012
sic-c012-1 = refl  -- c012 --r=1--> c011
sic-c012-2 : cls-of c010 ns-ds-c012-2 ≡ cls-of c012 ns-c012
sic-c012-2 = refl  -- c012 --r=2--> c010
sic-c020-0 : cls-of c020 ns-ds-c020-0 ≡ cls-of c020 ns-c020
sic-c020-0 = refl  -- c020 --r=0--> c020
sic-c020-1 : cls-of c020 ns-ds-c020-1 ≡ cls-of c020 ns-c020
sic-c020-1 = refl  -- c020 --r=1--> c020
sic-c020-2 : cls-of c020 ns-ds-c020-2 ≡ cls-of c020 ns-c020
sic-c020-2 = refl  -- c020 --r=2--> c020
sic-c021-0 : cls-of c021 ns-ds-c021-0 ≡ cls-of c021 ns-c021
sic-c021-0 = refl  -- c021 --r=0--> c021
sic-c021-1 : cls-of c021 ns-ds-c021-1 ≡ cls-of c021 ns-c021
sic-c021-1 = refl  -- c021 --r=1--> c021
sic-c021-2 : cls-of c021 ns-ds-c021-2 ≡ cls-of c021 ns-c021
sic-c021-2 = refl  -- c021 --r=2--> c021
sic-c022-0 : cls-of c022 ns-ds-c022-0 ≡ cls-of c022 ns-c022
sic-c022-0 = refl  -- c022 --r=0--> c022
sic-c022-1 : cls-of c022 ns-ds-c022-1 ≡ cls-of c022 ns-c022
sic-c022-1 = refl  -- c022 --r=1--> c022
sic-c022-2 : cls-of c022 ns-ds-c022-2 ≡ cls-of c022 ns-c022
sic-c022-2 = refl  -- c022 --r=2--> c022
sic-c101-0 : cls-of c101 ns-ds-c101-0 ≡ cls-of c101 ns-c101
sic-c101-0 = refl  -- c101 --r=0--> c101
sic-c101-1 : cls-of c120 ns-ds-c101-1 ≡ cls-of c101 ns-c101
sic-c101-1 = refl  -- c101 --r=1--> c120
sic-c101-2 : cls-of c111 ns-ds-c101-2 ≡ cls-of c101 ns-c101
sic-c101-2 = refl  -- c101 --r=2--> c111
sic-c102-0 : cls-of c102 ns-ds-c102-0 ≡ cls-of c102 ns-c102
sic-c102-0 = refl  -- c102 --r=0--> c102
sic-c102-1 : cls-of c121 ns-ds-c102-1 ≡ cls-of c102 ns-c102
sic-c102-1 = refl  -- c102 --r=1--> c121
sic-c102-2 : cls-of c112 ns-ds-c102-2 ≡ cls-of c102 ns-c102
sic-c102-2 = refl  -- c102 --r=2--> c112
sic-c111-0 : cls-of c111 ns-ds-c111-0 ≡ cls-of c111 ns-c111
sic-c111-0 = refl  -- c111 --r=0--> c111
sic-c111-1 : cls-of c101 ns-ds-c111-1 ≡ cls-of c111 ns-c111
sic-c111-1 = refl  -- c111 --r=1--> c101
sic-c111-2 : cls-of c120 ns-ds-c111-2 ≡ cls-of c111 ns-c111
sic-c111-2 = refl  -- c111 --r=2--> c120
sic-c112-0 : cls-of c112 ns-ds-c112-0 ≡ cls-of c112 ns-c112
sic-c112-0 = refl  -- c112 --r=0--> c112
sic-c112-1 : cls-of c102 ns-ds-c112-1 ≡ cls-of c112 ns-c112
sic-c112-1 = refl  -- c112 --r=1--> c102
sic-c112-2 : cls-of c121 ns-ds-c112-2 ≡ cls-of c112 ns-c112
sic-c112-2 = refl  -- c112 --r=2--> c121
sic-c120-0 : cls-of c120 ns-ds-c120-0 ≡ cls-of c120 ns-c120
sic-c120-0 = refl  -- c120 --r=0--> c120
sic-c120-1 : cls-of c111 ns-ds-c120-1 ≡ cls-of c120 ns-c120
sic-c120-1 = refl  -- c120 --r=1--> c111
sic-c120-2 : cls-of c101 ns-ds-c120-2 ≡ cls-of c120 ns-c120
sic-c120-2 = refl  -- c120 --r=2--> c101
sic-c121-0 : cls-of c121 ns-ds-c121-0 ≡ cls-of c121 ns-c121
sic-c121-0 = refl  -- c121 --r=0--> c121
sic-c121-1 : cls-of c112 ns-ds-c121-1 ≡ cls-of c121 ns-c121
sic-c121-1 = refl  -- c121 --r=1--> c112
sic-c121-2 : cls-of c102 ns-ds-c121-2 ≡ cls-of c121 ns-c121
sic-c121-2 = refl  -- c121 --r=2--> c102
sic-c201-0 : cls-of c201 ns-ds-c201-0 ≡ cls-of c201 ns-c201
sic-c201-0 = refl  -- c201 --r=0--> c201
sic-c201-1 : cls-of c211 ns-ds-c201-1 ≡ cls-of c201 ns-c201
sic-c201-1 = refl  -- c201 --r=1--> c211
sic-c201-2 : cls-of c222 ns-ds-c201-2 ≡ cls-of c201 ns-c201
sic-c201-2 = refl  -- c201 --r=2--> c222
sic-c202-0 : cls-of c202 ns-ds-c202-0 ≡ cls-of c202 ns-c202
sic-c202-0 = refl  -- c202 --r=0--> c202
sic-c202-1 : cls-of c212 ns-ds-c202-1 ≡ cls-of c202 ns-c202
sic-c202-1 = refl  -- c202 --r=1--> c212
sic-c202-2 : cls-of c220 ns-ds-c202-2 ≡ cls-of c202 ns-c202
sic-c202-2 = refl  -- c202 --r=2--> c220
sic-c211-0 : cls-of c211 ns-ds-c211-0 ≡ cls-of c211 ns-c211
sic-c211-0 = refl  -- c211 --r=0--> c211
sic-c211-1 : cls-of c222 ns-ds-c211-1 ≡ cls-of c211 ns-c211
sic-c211-1 = refl  -- c211 --r=1--> c222
sic-c211-2 : cls-of c201 ns-ds-c211-2 ≡ cls-of c211 ns-c211
sic-c211-2 = refl  -- c211 --r=2--> c201
sic-c212-0 : cls-of c212 ns-ds-c212-0 ≡ cls-of c212 ns-c212
sic-c212-0 = refl  -- c212 --r=0--> c212
sic-c212-1 : cls-of c220 ns-ds-c212-1 ≡ cls-of c212 ns-c212
sic-c212-1 = refl  -- c212 --r=1--> c220
sic-c212-2 : cls-of c202 ns-ds-c212-2 ≡ cls-of c212 ns-c212
sic-c212-2 = refl  -- c212 --r=2--> c202
sic-c220-0 : cls-of c220 ns-ds-c220-0 ≡ cls-of c220 ns-c220
sic-c220-0 = refl  -- c220 --r=0--> c220
sic-c220-1 : cls-of c202 ns-ds-c220-1 ≡ cls-of c220 ns-c220
sic-c220-1 = refl  -- c220 --r=1--> c202
sic-c220-2 : cls-of c212 ns-ds-c220-2 ≡ cls-of c220 ns-c220
sic-c220-2 = refl  -- c220 --r=2--> c212
sic-c222-0 : cls-of c222 ns-ds-c222-0 ≡ cls-of c222 ns-c222
sic-c222-0 = refl  -- c222 --r=0--> c222
sic-c222-1 : cls-of c201 ns-ds-c222-1 ≡ cls-of c222 ns-c222
sic-c222-1 = refl  -- c222 --r=1--> c201
sic-c222-2 : cls-of c211 ns-ds-c222-2 ≡ cls-of c222 ns-c222
sic-c222-2 = refl  -- c222 --r=2--> c211


--------------------------------------------------------------------------------
-- §2f. cls-trace 18 条（类内迹一致; oracle emit-iso 逐字）
--------------------------------------------------------------------------------

ct-c010 : tℤ c010 ≡ tℤ (rep-of cls0)
ct-c010 = refl
ct-c011 : tℤ c011 ≡ tℤ (rep-of cls0)
ct-c011 = refl
ct-c012 : tℤ c012 ≡ tℤ (rep-of cls0)
ct-c012 = refl
ct-c020 : tℤ c020 ≡ tℤ (rep-of cls5)
ct-c020 = refl
ct-c021 : tℤ c021 ≡ tℤ (rep-of cls6)
ct-c021 = refl
ct-c022 : tℤ c022 ≡ tℤ (rep-of cls7)
ct-c022 = refl
ct-c101 : tℤ c101 ≡ tℤ (rep-of cls1)
ct-c101 = refl
ct-c102 : tℤ c102 ≡ tℤ (rep-of cls2)
ct-c102 = refl
ct-c111 : tℤ c111 ≡ tℤ (rep-of cls1)
ct-c111 = refl
ct-c112 : tℤ c112 ≡ tℤ (rep-of cls2)
ct-c112 = refl
ct-c120 : tℤ c120 ≡ tℤ (rep-of cls1)
ct-c120 = refl
ct-c121 : tℤ c121 ≡ tℤ (rep-of cls2)
ct-c121 = refl
ct-c201 : tℤ c201 ≡ tℤ (rep-of cls3)
ct-c201 = refl
ct-c202 : tℤ c202 ≡ tℤ (rep-of cls4)
ct-c202 = refl
ct-c211 : tℤ c211 ≡ tℤ (rep-of cls3)
ct-c211 = refl
ct-c212 : tℤ c212 ≡ tℤ (rep-of cls4)
ct-c212 = refl
ct-c220 : tℤ c220 ≡ tℤ (rep-of cls4)
ct-c220 = refl
ct-c222 : tℤ c222 ≡ tℤ (rep-of cls3)
ct-c222 = refl


--------------------------------------------------------------------------------
-- §2g. 类互斥 28 条（oracle emit-iso 逐字）
--------------------------------------------------------------------------------

ne-cls0-1 : cls0 ≡ cls1 → ⊥
ne-cls0-1 ()
ne-cls0-2 : cls0 ≡ cls2 → ⊥
ne-cls0-2 ()
ne-cls0-3 : cls0 ≡ cls3 → ⊥
ne-cls0-3 ()
ne-cls0-4 : cls0 ≡ cls4 → ⊥
ne-cls0-4 ()
ne-cls0-5 : cls0 ≡ cls5 → ⊥
ne-cls0-5 ()
ne-cls0-6 : cls0 ≡ cls6 → ⊥
ne-cls0-6 ()
ne-cls0-7 : cls0 ≡ cls7 → ⊥
ne-cls0-7 ()
ne-cls1-2 : cls1 ≡ cls2 → ⊥
ne-cls1-2 ()
ne-cls1-3 : cls1 ≡ cls3 → ⊥
ne-cls1-3 ()
ne-cls1-4 : cls1 ≡ cls4 → ⊥
ne-cls1-4 ()
ne-cls1-5 : cls1 ≡ cls5 → ⊥
ne-cls1-5 ()
ne-cls1-6 : cls1 ≡ cls6 → ⊥
ne-cls1-6 ()
ne-cls1-7 : cls1 ≡ cls7 → ⊥
ne-cls1-7 ()
ne-cls2-3 : cls2 ≡ cls3 → ⊥
ne-cls2-3 ()
ne-cls2-4 : cls2 ≡ cls4 → ⊥
ne-cls2-4 ()
ne-cls2-5 : cls2 ≡ cls5 → ⊥
ne-cls2-5 ()
ne-cls2-6 : cls2 ≡ cls6 → ⊥
ne-cls2-6 ()
ne-cls2-7 : cls2 ≡ cls7 → ⊥
ne-cls2-7 ()
ne-cls3-4 : cls3 ≡ cls4 → ⊥
ne-cls3-4 ()
ne-cls3-5 : cls3 ≡ cls5 → ⊥
ne-cls3-5 ()
ne-cls3-6 : cls3 ≡ cls6 → ⊥
ne-cls3-6 ()
ne-cls3-7 : cls3 ≡ cls7 → ⊥
ne-cls3-7 ()
ne-cls4-5 : cls4 ≡ cls5 → ⊥
ne-cls4-5 ()
ne-cls4-6 : cls4 ≡ cls6 → ⊥
ne-cls4-6 ()
ne-cls4-7 : cls4 ≡ cls7 → ⊥
ne-cls4-7 ()
ne-cls5-6 : cls5 ≡ cls6 → ⊥
ne-cls5-6 ()
ne-cls5-7 : cls5 ≡ cls7 → ⊥
ne-cls5-7 ()
ne-cls6-7 : cls6 ≡ cls7 → ⊥
ne-cls6-7 ()

