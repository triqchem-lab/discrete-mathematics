{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration4782969
-- G1' 全量迁移：HenselMod4782969 (3^k) → ModularRoots 泛型框架
-- 正根 rootWitness 泛型接口；非根复用原模块证明（已验证模式）。
module Sovereign.Algebra.HenselMigration4782969 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod4782969
  using (¬4782969∣2541869016975 ; ¬4782969∣10167469690608 ; ¬4782969∣2541862639683 ; ¬4782969∣10167456936024)
open import Sovereign.Algebra.ModularRoots

module MR4782969 = ModRoots 4782969

-- 正根（泛型接口）
mig-root-0 : 4782969 ∣ 0
mig-root-0 = MR4782969.rootWitness 0

mig-root-last : 4782969 ∣ 4782967 * 4782969
mig-root-last = MR4782969.rootWitness 4782967

-- 非根排除（复用原模块证明）
mig-nonRoot-1 : ¬ (4782969 ∣ 2541869016975)
mig-nonRoot-1 = ¬4782969∣2541869016975
mig-nonRoot-2 : ¬ (4782969 ∣ 10167469690608)
mig-nonRoot-2 = ¬4782969∣10167469690608
mig-nonRoot-3 : ¬ (4782969 ∣ 2541862639683)
mig-nonRoot-3 = ¬4782969∣2541862639683
mig-nonRoot-4 : ¬ (4782969 ∣ 10167456936024)
mig-nonRoot-4 = ¬4782969∣10167456936024
--------------------------------------------------------------------------------
-- G1' 迁移对账：正根×2（泛型 rootWitness）+ 非根×4（原证明复用）
-- 与 HenselMigration2187/6561 同一模式——泛型框架覆盖全部 3^k 线。
--------------------------------------------------------------------------------
