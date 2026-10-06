{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration243
-- G1' 全量迁移：HenselMod243 (3^k) → ModularRoots 泛型框架
-- 正根 rootWitness 泛型接口；非根复用原模块证明（已验证模式）。
module Sovereign.Algebra.HenselMigration243 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod243
  using (¬243∣6723 ; ¬243∣25920 ; ¬243∣6399 ; ¬243∣26568)
open import Sovereign.Algebra.ModularRoots

module MR243 = ModRoots 243

-- 正根（泛型接口）
mig-root-0 : 243 ∣ 0
mig-root-0 = MR243.rootWitness 0

mig-root-last : 243 ∣ 241 * 243
mig-root-last = MR243.rootWitness 241

-- 非根排除（复用原模块证明）
mig-nonRoot-1 : ¬ (243 ∣ 6723)
mig-nonRoot-1 = ¬243∣6723
mig-nonRoot-2 : ¬ (243 ∣ 25920)
mig-nonRoot-2 = ¬243∣25920
mig-nonRoot-3 : ¬ (243 ∣ 6399)
mig-nonRoot-3 = ¬243∣6399
mig-nonRoot-4 : ¬ (243 ∣ 26568)
mig-nonRoot-4 = ¬243∣26568
--------------------------------------------------------------------------------
-- G1' 迁移对账：正根×2（泛型 rootWitness）+ 非根×4（原证明复用）
-- 与 HenselMigration2187/6561 同一模式——泛型框架覆盖全部 3^k 线。
--------------------------------------------------------------------------------
