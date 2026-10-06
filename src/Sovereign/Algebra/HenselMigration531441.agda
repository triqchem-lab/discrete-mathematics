{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration531441
-- G1' 全量迁移：HenselMod531441 (3^k) → ModularRoots 泛型框架
-- 正根 rootWitness 泛型接口；非根复用原模块证明（已验证模式）。
module Sovereign.Algebra.HenselMigration531441 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod531441
  using (¬531441∣31381413903 ; ¬531441∣125524947024 ; ¬531441∣31380705315 ; ¬531441∣125523529848)
open import Sovereign.Algebra.ModularRoots

module MR531441 = ModRoots 531441

-- 正根（泛型接口）
mig-root-0 : 531441 ∣ 0
mig-root-0 = MR531441.rootWitness 0

mig-root-last : 531441 ∣ 531439 * 531441
mig-root-last = MR531441.rootWitness 531439

-- 非根排除（复用原模块证明）
mig-nonRoot-1 : ¬ (531441 ∣ 31381413903)
mig-nonRoot-1 = ¬531441∣31381413903
mig-nonRoot-2 : ¬ (531441 ∣ 125524947024)
mig-nonRoot-2 = ¬531441∣125524947024
mig-nonRoot-3 : ¬ (531441 ∣ 31380705315)
mig-nonRoot-3 = ¬531441∣31380705315
mig-nonRoot-4 : ¬ (531441 ∣ 125523529848)
mig-nonRoot-4 = ¬531441∣125523529848
--------------------------------------------------------------------------------
-- G1' 迁移对账：正根×2（泛型 rootWitness）+ 非根×4（原证明复用）
-- 与 HenselMigration2187/6561 同一模式——泛型框架覆盖全部 3^k 线。
--------------------------------------------------------------------------------
