{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration1594323
-- G1' 全量迁移：HenselMod1594323 (3^k) → ModularRoots 泛型框架
-- 正根 rootWitness 泛型接口；非根复用原模块证明（已验证模式）。
module Sovereign.Algebra.HenselMigration1594323 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod1594323
  using (¬1594323∣282430599363 ; ¬1594323∣1129720271688 ; ¬1594323∣282428473599 ; ¬1594323∣1129716020160)
open import Sovereign.Algebra.ModularRoots

module MR1594323 = ModRoots 1594323

-- 正根（泛型接口）
mig-root-0 : 1594323 ∣ 0
mig-root-0 = MR1594323.rootWitness 0

mig-root-last : 1594323 ∣ 1594321 * 1594323
mig-root-last = MR1594323.rootWitness 1594321

-- 非根排除（复用原模块证明）
mig-nonRoot-1 : ¬ (1594323 ∣ 282430599363)
mig-nonRoot-1 = ¬1594323∣282430599363
mig-nonRoot-2 : ¬ (1594323 ∣ 1129720271688)
mig-nonRoot-2 = ¬1594323∣1129720271688
mig-nonRoot-3 : ¬ (1594323 ∣ 282428473599)
mig-nonRoot-3 = ¬1594323∣282428473599
mig-nonRoot-4 : ¬ (1594323 ∣ 1129716020160)
mig-nonRoot-4 = ¬1594323∣1129716020160
--------------------------------------------------------------------------------
-- G1' 迁移对账：正根×2（泛型 rootWitness）+ 非根×4（原证明复用）
-- 与 HenselMigration2187/6561 同一模式——泛型框架覆盖全部 3^k 线。
--------------------------------------------------------------------------------
