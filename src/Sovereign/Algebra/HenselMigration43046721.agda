{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration43046721
-- G1' 全量迁移：HenselMod43046721 (3^k) → ModularRoots 泛型框架
-- 正根 rootWitness 泛型接口；非根复用原模块证明（已验证模式）。
module Sovereign.Algebra.HenselMigration43046721 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod43046721
  using (¬43046721∣205891160792463 ; ¬43046721∣823564585774224 ; ¬43046721∣205891103396835 ; ¬43046721∣823564528378595)
open import Sovereign.Algebra.ModularRoots

module MR43046721 = ModRoots 43046721

-- 正根（泛型接口）
mig-root-0 : 43046721 ∣ 0
mig-root-0 = MR43046721.rootWitness 0

mig-root-last : 43046721 ∣ 43046719 * 43046721
mig-root-last = MR43046721.rootWitness 43046719

-- 非根排除（复用原模块证明）
mig-nonRoot-1 : ¬ (43046721 ∣ 205891160792463)
mig-nonRoot-1 = ¬43046721∣205891160792463
mig-nonRoot-2 : ¬ (43046721 ∣ 823564585774224)
mig-nonRoot-2 = ¬43046721∣823564585774224
mig-nonRoot-3 : ¬ (43046721 ∣ 205891103396835)
mig-nonRoot-3 = ¬43046721∣205891103396835
mig-nonRoot-4 : ¬ (43046721 ∣ 823564528378595)
mig-nonRoot-4 = ¬43046721∣823564528378595
--------------------------------------------------------------------------------
-- G1' 迁移对账：正根×2（泛型 rootWitness）+ 非根×4（原证明复用）
-- 与 HenselMigration2187/6561 同一模式——泛型框架覆盖全部 3^k 线。
--------------------------------------------------------------------------------
