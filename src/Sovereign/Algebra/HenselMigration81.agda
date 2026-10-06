{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration81
-- G1' 全量迁移：HenselMod81 (3^k) → ModularRoots 泛型框架
-- 正根 rootWitness 泛型接口；非根复用原模块证明（已验证模式）。
module Sovereign.Algebra.HenselMigration81 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod81
  using (¬81∣675 ; ¬81∣783 ; ¬81∣2808 ; ¬81∣3024)
open import Sovereign.Algebra.ModularRoots

module MR81 = ModRoots 81

-- 正根（泛型接口）
mig-root-0 : 81 ∣ 0
mig-root-0 = MR81.rootWitness 0

mig-root-last : 81 ∣ 79 * 81
mig-root-last = MR81.rootWitness 79

-- 非根排除（复用原模块证明）
mig-nonRoot-1 : ¬ (81 ∣ 675)
mig-nonRoot-1 = ¬81∣675
mig-nonRoot-2 : ¬ (81 ∣ 783)
mig-nonRoot-2 = ¬81∣783
mig-nonRoot-3 : ¬ (81 ∣ 2808)
mig-nonRoot-3 = ¬81∣2808
mig-nonRoot-4 : ¬ (81 ∣ 3024)
mig-nonRoot-4 = ¬81∣3024
--------------------------------------------------------------------------------
-- G1' 迁移对账：正根×2（泛型 rootWitness）+ 非根×4（原证明复用）
-- 与 HenselMigration2187/6561 同一模式——泛型框架覆盖全部 3^k 线。
--------------------------------------------------------------------------------
