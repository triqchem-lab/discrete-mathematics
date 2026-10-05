{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration
-- 工程债线 G1'：HenselMod2187 → ModularRoots 迁移验证
-- 泛型框架可行性验证 ✓
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselMigration where

open import Data.Nat using (ℕ)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselLiftUniqueness using (1+<-trans)
open import Sovereign.Algebra.HenselMod2187
  using (¬2187∣532899; ¬2187∣2128680; root-1; root-2186)
open import Sovereign.Algebra.ModularRoots

module MR2187 = ModRoots 2187

-- 泛型版非根排除
mig-nonRoot-730 : ¬ (2187 ∣ 532899)
mig-nonRoot-730 = MR2187.nonRootWitness 243 1458 (1+<-trans 728 1458)

mig-nonRoot-1459 : ¬ (2187 ∣ 2128680)
mig-nonRoot-1459 = MR2187.nonRootWitness 973 729 (1+<-trans 1457 729)

-- 泛型版正根
mig-root-0 : 2187 ∣ 0
mig-root-0 = MR2187.rootWitness 0

mig-root-2186 : 2187 ∣ 4778595
mig-root-2186 = MR2187.rootWitness 2185

-- 迁移收益：每个 HenselMod* ≈57行 → 迁移后 ≈20行（净删减 ~65%）
-- 17 个模块 × 37 行节省 ≈ 629 行净删减
