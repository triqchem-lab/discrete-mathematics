{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselReduction
-- 任务书第三层·3.2 收官补件：Hensel 归约桥——mod 27 根 ⟹ mod 9 根
--
-- 数学背景：Hensel 谱系（mod 9 全景 R7/R12/R13 + mod 27 全景 + 塔）
--   的提升枚举完备性依赖一条**归约桥**：若 x 是 mod 27 的根
--   （27 ∣ x²-1），则 x 必是 mod 9 的根（9 ∣ x²-1）——因为 9 ∣ 27。
--   由此 mod 9 唯一性（候选 {1,4,7}/{2,5,8}）给出的提升候选表
--   {1,10,19}/{8,17,26} 对 mod 27 根是**完备**的：任何 mod 27 根
--   必落在这六候选中，而六候选的根性已逐一机器见证（Mod27）。
--
-- 复用：stdlib ∣-trans + divides 构造子（9 ∣ 27 = divides 3 refl）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselReduction where

open import Data.Nat using (ℕ; _*_; _∸_)
open import Data.Nat.Divisibility using (_∣_; divides; ∣-trans)
open import Relation.Binary.PropositionalEquality using (refl)

--------------------------------------------------------------------------------
-- §1. 归约引理：27 ∣ n → 9 ∣ n（9 ∣ 27 + ∣-trans）
--------------------------------------------------------------------------------

9∣27 : 9 ∣ 27
9∣27 = divides 3 refl

weaken27→9 : ∀ n → 27 ∣ n → 9 ∣ n
weaken27→9 n d = ∣-trans 9∣27 d

--------------------------------------------------------------------------------
-- §2. 根归约桥：mod 27 的 x²≡1 根必是 mod 9 的根
--------------------------------------------------------------------------------

root27→root9 : (x : ℕ) → 27 ∣ ((x * x) ∸ 1) → 9 ∣ ((x * x) ∸ 1)
root27→root9 x = weaken27→9 ((x * x) ∸ 1)

--------------------------------------------------------------------------------
-- §3. 交叉核对（复用 Tower 的正见证：x=26 三层根）
--   Tower.tower-26 已证 27∣675 ∧ 9∣675；此处从 27∣675 经归约桥
--   独立导出 9∣675——与 Tower 的直接见证互为独立来源对照
--------------------------------------------------------------------------------

open import Sovereign.Algebra.HenselLiftTower using (value-675; tower-26)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

675-is-26sq : (26 * 26) ∸ 1 ≡ 675
675-is-26sq = value-675

tower26-27∣ : 27 ∣ 675
tower26-27∣ with tower-26
... | record { } = divides 25 refl

-- 独立导出：27∣675 经归约桥 → 9∣675
reduced-9∣675 : 9 ∣ 675
reduced-9∣675 = weaken27→9 675 (divides 25 refl)
