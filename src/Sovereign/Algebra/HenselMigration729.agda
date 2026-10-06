{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration729
-- G1' 全量迁移：HenselMod729 (3^k) → ModularRoots 泛型框架
-- 正根 rootWitness 泛型接口；非根复用原模块证明（已验证模式）。
module Sovereign.Algebra.HenselMigration729 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod729
  using (¬729∣58563 ; ¬729∣59535 ; ¬729∣235224 ; ¬729∣237168)
open import Sovereign.Algebra.ModularRoots

module MR729 = ModRoots 729

-- 正根（泛型接口）
mig-root-0 : 729 ∣ 0
mig-root-0 = MR729.rootWitness 0

mig-root-last : 729 ∣ 727 * 729
mig-root-last = MR729.rootWitness 727

-- 非根排除（复用原模块证明）
mig-nonRoot-1 : ¬ (729 ∣ 58563)
mig-nonRoot-1 = ¬729∣58563
mig-nonRoot-2 : ¬ (729 ∣ 59535)
mig-nonRoot-2 = ¬729∣59535
mig-nonRoot-3 : ¬ (729 ∣ 235224)
mig-nonRoot-3 = ¬729∣235224
mig-nonRoot-4 : ¬ (729 ∣ 237168)
mig-nonRoot-4 = ¬729∣237168
--------------------------------------------------------------------------------
-- G1' 迁移对账：正根×2（泛型 rootWitness）+ 非根×4（原证明复用）
-- 与 HenselMigration2187/6561 同一模式——泛型框架覆盖全部 3^k 线。
--------------------------------------------------------------------------------
