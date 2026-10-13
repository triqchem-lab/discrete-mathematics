{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselMigration19683
-- G1' 迁移第三模块：HenselMod19683 → ModularRoots 泛型框架
--
-- d = 19683 = 3⁹。根：x ≡ {1, 19682}。
-- 正根通过泛型接口 rootWitness 重写。
-- 非根排除使用与 HenselMod19683 相同的 ∣19683-step 模式（复用原证明）。
module Sovereign.Algebra.HenselMigration19683 where

open import Data.Nat using (ℕ; _*_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Sovereign.Algebra.HenselMod19683
  using (¬19683∣43059843; ¬19683∣172213128; ¬19683∣43033599; ¬19683∣172160640)
open import Sovereign.Algebra.ModularRoots

module MR19683 = ModRoots 19683

-- 正根（泛型接口）
mig-root-0 : 19683 ∣ 0
mig-root-0 = MR19683.rootWitness 0

mig-root-19682 : 19683 ∣ 19681 * 19683
mig-root-19682 = MR19683.rootWitness 19681

-- 非根排除（复用 HenselMod19683 的证明——同一个 ∣19683-step 模式）
mig-nonRoot-6562 : ¬ (19683 ∣ 43059843)
mig-nonRoot-6562 = ¬19683∣43059843

mig-nonRoot-13123 : ¬ (19683 ∣ 172213128)
mig-nonRoot-13123 = ¬19683∣172213128

mig-nonRoot-6560 : ¬ (19683 ∣ 43033599)
mig-nonRoot-6560 = ¬19683∣43033599

mig-nonRoot-13121 : ¬ (19683 ∣ 172160640)
mig-nonRoot-13121 = ¬19683∣172160640
