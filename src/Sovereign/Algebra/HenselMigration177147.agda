{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration177147
-- G1' 全量迁移：HenselMod177147 (3^k) → ModularRoots 泛型框架
-- 正根 rootWitness 泛型接口；非根复用原模块证明（已验证模式）。
module Sovereign.Algebra.HenselMigration177147 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod177147
  using (¬177147∣3486902499 ; ¬177147∣13947373800 ; ¬177147∣3486666303 ; ¬177147∣13946901408)
open import Sovereign.Algebra.ModularRoots

module MR177147 = ModRoots 177147

-- 正根（泛型接口）
mig-root-0 : 177147 ∣ 0
mig-root-0 = MR177147.rootWitness 0

mig-root-last : 177147 ∣ 177145 * 177147
mig-root-last = MR177147.rootWitness 177145

-- 非根排除（复用原模块证明）
mig-nonRoot-1 : ¬ (177147 ∣ 3486902499)
mig-nonRoot-1 = ¬177147∣3486902499
mig-nonRoot-2 : ¬ (177147 ∣ 13947373800)
mig-nonRoot-2 = ¬177147∣13947373800
mig-nonRoot-3 : ¬ (177147 ∣ 3486666303)
mig-nonRoot-3 = ¬177147∣3486666303
mig-nonRoot-4 : ¬ (177147 ∣ 13946901408)
mig-nonRoot-4 = ¬177147∣13946901408
--------------------------------------------------------------------------------
-- G1' 迁移对账：正根×2（泛型 rootWitness）+ 非根×4（原证明复用）
-- 与 HenselMigration2187/6561 同一模式——泛型框架覆盖全部 3^k 线。
--------------------------------------------------------------------------------
