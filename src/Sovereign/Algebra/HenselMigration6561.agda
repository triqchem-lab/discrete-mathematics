{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration6561
-- G1' 迁移第二模块：HenselMod6561 → ModularRoots 泛型框架
--
-- d = 6561 = 3⁸。根：x ≡ {1, 6560}。
-- 正根通过泛型接口 rootWitness 重写。
-- 非根排除使用与 HenselMod6561 相同的 ∣6561-step 模式（复用原证明）。
module Sovereign.Algebra.HenselMigration6561 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod6561
  using (¬6561∣4787343; ¬6561∣19140624; ¬6561∣4778595; ¬6561∣19131875)
open import Sovereign.Algebra.ModularRoots

module MR6561 = ModRoots 6561

-- 正根（泛型接口）
mig-root-0 : 6561 ∣ 0
mig-root-0 = MR6561.rootWitness 0

mig-root-6560 : 6561 ∣ 6560 * 6561
mig-root-6560 = MR6561.rootWitness 6560

-- 非根排除（复用 HenselMod6561 的证明——同一个 ∣6561-step 模式）
mig-nonRoot-2188 : ¬ (6561 ∣ 4787343)
mig-nonRoot-2188 = ¬6561∣4787343

mig-nonRoot-4375 : ¬ (6561 ∣ 19140624)
mig-nonRoot-4375 = ¬6561∣19140624

mig-nonRoot-2186 : ¬ (6561 ∣ 4778595)
mig-nonRoot-2186 = ¬6561∣4778595

mig-nonRoot-4374 : ¬ (6561 ∣ 19131875)
mig-nonRoot-4374 = ¬6561∣19131875
