{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration59049
-- G1' 全量迁移：HenselMod59049 (3^k) → ModularRoots 泛型框架
-- 正根 rootWitness 泛型接口；非根复用原模块证明（已验证模式）。
module Sovereign.Algebra.HenselMigration59049 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod59049
  using (¬59049∣387459855 ; ¬59049∣1549760688 ; ¬59049∣387381123 ; ¬59049∣1549603224)
open import Sovereign.Algebra.ModularRoots

module MR59049 = ModRoots 59049

-- 正根（泛型接口）
mig-root-0 : 59049 ∣ 0
mig-root-0 = MR59049.rootWitness 0

mig-root-last : 59049 ∣ 59047 * 59049
mig-root-last = MR59049.rootWitness 59047

-- 非根排除（复用原模块证明）
mig-nonRoot-1 : ¬ (59049 ∣ 387459855)
mig-nonRoot-1 = ¬59049∣387459855
mig-nonRoot-2 : ¬ (59049 ∣ 1549760688)
mig-nonRoot-2 = ¬59049∣1549760688
mig-nonRoot-3 : ¬ (59049 ∣ 387381123)
mig-nonRoot-3 = ¬59049∣387381123
mig-nonRoot-4 : ¬ (59049 ∣ 1549603224)
mig-nonRoot-4 = ¬59049∣1549603224
--------------------------------------------------------------------------------
-- G1' 迁移对账：正根×2（泛型 rootWitness）+ 非根×4（原证明复用）
-- 与 HenselMigration2187/6561 同一模式——泛型框架覆盖全部 3^k 线。
--------------------------------------------------------------------------------
