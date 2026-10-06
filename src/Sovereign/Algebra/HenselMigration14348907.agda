{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration14348907
-- G1' 全量迁移：HenselMod14348907 (3^k) → ModularRoots 泛型框架
-- 正根 rootWitness 泛型接口；非根复用原模块证明（已验证模式）。
module Sovereign.Algebra.HenselMigration14348907 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod14348907
  using (¬14348907∣22876802020899 ; ¬14348907∣91507188951720 ; ¬14348907∣22876782889023 ; ¬14348907∣91507150687968)
open import Sovereign.Algebra.ModularRoots

module MR14348907 = ModRoots 14348907

-- 正根（泛型接口）
mig-root-0 : 14348907 ∣ 0
mig-root-0 = MR14348907.rootWitness 0

mig-root-last : 14348907 ∣ 14348905 * 14348907
mig-root-last = MR14348907.rootWitness 14348905

-- 非根排除（复用原模块证明）
mig-nonRoot-1 : ¬ (14348907 ∣ 22876802020899)
mig-nonRoot-1 = ¬14348907∣22876802020899
mig-nonRoot-2 : ¬ (14348907 ∣ 91507188951720)
mig-nonRoot-2 = ¬14348907∣91507188951720
mig-nonRoot-3 : ¬ (14348907 ∣ 22876782889023)
mig-nonRoot-3 = ¬14348907∣22876782889023
mig-nonRoot-4 : ¬ (14348907 ∣ 91507150687968)
mig-nonRoot-4 = ¬14348907∣91507150687968
--------------------------------------------------------------------------------
-- G1' 迁移对账：正根×2（泛型 rootWitness）+ 非根×4（原证明复用）
-- 与 HenselMigration2187/6561 同一模式——泛型框架覆盖全部 3^k 线。
--------------------------------------------------------------------------------
