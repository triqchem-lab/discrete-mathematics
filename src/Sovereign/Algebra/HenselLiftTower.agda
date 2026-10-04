{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselLiftTower
-- 任务书第三层·3.2 延伸：Hensel **塔**实例（x² ≡ 1 的 p 幂链 3 → 9 → 27）
--
-- 数学背景：Hensel 提升的塔结构——根 x=1 在 mod 3、mod 9、mod 27 上
--   逐层保持（27∣0 平凡但链式陈述完整）；根 x=26 ≡ -1 (mod 27) 在
--   三层同时是根（3∣675, 9∣675, 27∣675，商 225/75/25）。
--
--   与 R7/R12/R13 的关系：R7 闭合 mod 9 存在性，R12/R13 闭合 mod 9
--   唯一性（排除枚举）。本模块把塔推到 mod 27（存在性层），展示
--   p 幂模式的三层结构。
--
-- ⚠ 诚实边界：存在性见证（整除的 divides 构造）；mod 27 的唯一性
--   否证（x=10: ¬(27∣99) 等，商到 3）roadmap。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselLiftTower where

open import Data.Nat using (ℕ; _*_; _∸_)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- §1. 根 x = 1 的塔：3∣0, 9∣0, 27∣0 逐层保持
--------------------------------------------------------------------------------

tower-1 : (3 ∣ ((1 * 1) ∸ 1)) × (9 ∣ ((1 * 1) ∸ 1)) × (27 ∣ ((1 * 1) ∸ 1))
tower-1 = divides 0 refl , divides 0 refl , divides 0 refl

--------------------------------------------------------------------------------
-- §2. 根 x = 26 ≡ -1 (mod 27) 的塔：三层同时整除
--
--   26² - 1 = 675 = 225·3 = 75·9 = 25·27
--------------------------------------------------------------------------------

tower-26 : (3 ∣ ((26 * 26) ∸ 1)) × (9 ∣ ((26 * 26) ∸ 1)) × (27 ∣ ((26 * 26) ∸ 1))
tower-26 = divides 225 refl , divides 75 refl , divides 25 refl

-- 数值锚：675 的三层分解（refl 计算闭合）
value-675 : (26 * 26) ∸ 1 ≡ 675
value-675 = refl

-- 27 层的商：675 = 25·27
quotient-27 : 675 ≡ 25 * 27
quotient-27 = refl
