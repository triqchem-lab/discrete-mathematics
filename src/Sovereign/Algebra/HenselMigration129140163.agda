{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration129140163
-- G1' 全量迁移：HenselMod129140163 (3^k) → ModularRoots 泛型框架
-- 正根 rootWitness 泛型接口；非根复用原模块证明（已验证模式）。
module Sovereign.Algebra.HenselMigration129140163 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod129140163
  using (¬129140163∣1853020274945283 ; ¬129140163∣7412080927594248 ; ¬129140163∣1853020102758399 ; ¬129140163∣7412080755407363)
open import Sovereign.Algebra.ModularRoots

module MR129140163 = ModRoots 129140163

-- 正根（泛型接口）
mig-root-0 : 129140163 ∣ 0
mig-root-0 = MR129140163.rootWitness 0

mig-root-last : 129140163 ∣ 129140161 * 129140163
mig-root-last = MR129140163.rootWitness 129140161

-- 非根排除（复用原模块证明）
mig-nonRoot-1 : ¬ (129140163 ∣ 1853020274945283)
mig-nonRoot-1 = ¬129140163∣1853020274945283
mig-nonRoot-2 : ¬ (129140163 ∣ 7412080927594248)
mig-nonRoot-2 = ¬129140163∣7412080927594248
mig-nonRoot-3 : ¬ (129140163 ∣ 1853020102758399)
mig-nonRoot-3 = ¬129140163∣1853020102758399
mig-nonRoot-4 : ¬ (129140163 ∣ 7412080755407363)
mig-nonRoot-4 = ¬129140163∣7412080755407363
--------------------------------------------------------------------------------
-- G1' 迁移对账：正根×2（泛型 rootWitness）+ 非根×4（原证明复用）
-- 与 HenselMigration2187/6561 同一模式——泛型框架覆盖全部 3^k 线。
--------------------------------------------------------------------------------
