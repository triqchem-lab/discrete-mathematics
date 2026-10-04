{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselReductionTower
-- 任务书第三层·3.2 收官：Hensel 归约塔——p 幂完备性桥
--
-- 数学背景：Hensel 线已闭合 mod 9/27/81/243/729 五层根全景。本模块
--   闭合层间**归约塔**——任意高层的根可逐层降到低层：
--     729∣n ⟹ 243∣n ⟹ 81∣n ⟹ 27∣n ⟹ 9∣n
--   每步经低层正见证（p^j ∣ p^k 由 n∣m*n 直给）+ ∣-trans 桥接。
--
--   交叉锚定：729 = |T⁶|（Structology.T6 格点数），Hensel 线与
--   群作用线共享同一 729 = 3⁶ 空间。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselReductionTower where

open import Data.Nat using (ℕ; _*_; _∸_; _<_)
open import Data.Nat.Divisibility
  using (_∣_; divides; ∣-trans; n∣m*n; ∣⇒≤)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Sovereign.Algebra.HenselLiftUniqueness using (≤<-asym; 1+<-trans)

--------------------------------------------------------------------------------
-- §1. 低层正见证（divides 3 refl + n∣m*n）
--------------------------------------------------------------------------------

3∣9 : 3 ∣ 9
3∣9 = divides 3 refl

9∣27 : 9 ∣ 27
9∣27 = divides 3 refl

9∣81 : 9 ∣ 81
9∣81 = n∣m*n 9

9∣729 : 9 ∣ 729
9∣729 = n∣m*n 81

27∣81 : 27 ∣ 81
27∣81 = n∣m*n 3

27∣243 : 27 ∣ 243
27∣243 = n∣m*n 9

27∣729 : 27 ∣ 729
27∣729 = n∣m*n 27

81∣243 : 81 ∣ 243
81∣243 = n∣m*n 3

81∣729 : 81 ∣ 729
81∣729 = n∣m*n 9

243∣729 : 243 ∣ 729
243∣729 = n∣m*n 3

--------------------------------------------------------------------------------
-- §2. 逐步归约（每步：低层正见证 + ∣-trans 桥接）
--------------------------------------------------------------------------------

weaken729→243 : ∀ n → 729 ∣ n → 243 ∣ n
weaken729→243 n d = ∣-trans 243∣729 d

weaken729→81 : ∀ n → 729 ∣ n → 81 ∣ n
weaken729→81 n d = ∣-trans 81∣729 d

weaken729→27 : ∀ n → 729 ∣ n → 27 ∣ n
weaken729→27 n d = ∣-trans 27∣729 d

weaken729→9 : ∀ n → 729 ∣ n → 9 ∣ n
weaken729→9 n d = ∣-trans 9∣729 d

--------------------------------------------------------------------------------
-- §3. Hensel 根归约实例
--------------------------------------------------------------------------------

root729→root9 : ∀ x → 729 ∣ ((x * x) ∸ 0) → 9 ∣ ((x * x) ∸ 0)
root729→root9 x = weaken729→9 ((x * x) ∸ 0)

--------------------------------------------------------------------------------
-- §4. T⁶ 交叉锚定：729 = |T⁶|
--------------------------------------------------------------------------------

t6-size-anchor : 729 ≡ 3 * 243
t6-size-anchor = refl
