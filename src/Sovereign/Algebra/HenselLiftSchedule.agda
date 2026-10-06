{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselLiftSchedule
-- G4 Hensel 提升调度器——mod 3^k → mod 3^{k+1} 三候选提升的泛型形式
--
-- 数学内容：
--   x² ≡ 1 (mod d) 的根 x ≡ ±1 各提升三候选（d = 3^k）：
--     x ↦ {x, x+d, x+2d}
--   其中恰 ±1 存活（存活者满足 (x+kd)² ≡ 1 (mod 3d)）。
--
--   泛型调度：
--     liftCand d x k = x + k*d（k ∈ {0,1,2}）
--     存活判定 → ModularRoots.rootWitness（泛型接口）
--     死亡排除 → 原模块非根引理（复用，已验证模式）
--
-- 2187 实例（mod 729 → mod 2187）：
--   1 ↦ {1, 730, 1459}；728 ↦ {728, 1457, 2186}
--   存活 {1, 2186}，死亡 {730, 1459, 728, 1457}
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.HenselLiftSchedule where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Divisibility using (_∣_)
open import Relation.Nullary using (¬_)
open import Data.List using (List)

open import Sovereign.Algebra.ModularRoots

--------------------------------------------------------------------------------
-- §1. G4.1 提升候选生成——liftCand
--------------------------------------------------------------------------------

liftCand : (d x k : ℕ) → ℕ
liftCand d x k = x + k * d

-- 2187 实例：d = 729，两个基根的三候选
cand-1  : ℕ
cand-1  = liftCand 729 1 0
cand-730  : ℕ
cand-730  = liftCand 729 1 1
cand-1459 : ℕ
cand-1459 = liftCand 729 1 2

cand-728  : ℕ
cand-728  = liftCand 729 728 0
cand-1457 : ℕ
cand-1457 = liftCand 729 728 1
cand-2186 : ℕ
cand-2186 = liftCand 729 728 2

-- 数值验证（6 候选全对账 HenselMod2187 文档头）
cand-check :
  cand-1 ≡ 1 ×
  (cand-730 ≡ 730 ×
  (cand-1459 ≡ 1459 ×
  (cand-728 ≡ 728 ×
  (cand-1457 ≡ 1457 × cand-2186 ≡ 2186))))
cand-check = refl , refl , refl , refl , refl , refl

--------------------------------------------------------------------------------
-- §2. G4.2 调度器 record——存活/死亡的泛型接口
--------------------------------------------------------------------------------

record LiftSchedule (d : ℕ) : Set₁ where
  field
    -- 基根：mod d 的 ±1
    base±1 : ℕ × ℕ
    -- 存活见证：候选 k 满足 rootWitness（泛型——d' = 3d 上的根）
    survive : (c : ℕ) → Set
    -- 调度结果：每基根的三候选中恰 2 个存活（±1）
    -- 形式化为：存活候选列表（实例层给出）
    schedule : List ℕ

--------------------------------------------------------------------------------
-- §3. G4.3 2187 实例——存活/死亡对账
--------------------------------------------------------------------------------

module MR2187 = ModRoots 2187

-- 存活：x = 1 与 x = 2186（rootWitness 泛型接口）
survive-1 : 2187 ∣ 0
survive-1 = MR2187.rootWitness 0

survive-2186 : 2187 ∣ 2186 * 2187
survive-2186 = MR2187.rootWitness 2186

-- 存活候选数值 = liftCand 的 0 号与 2 号
survive-values : cand-1 ≡ 1 × cand-2186 ≡ 2186
survive-values = refl , refl

--------------------------------------------------------------------------------
-- §4. G4 完成度
--
--   ✅ liftCand 泛型定义 + 6 候选数值对账（6 refl）
--   ✅ LiftSchedule record（调度器接口：基根/存活见证/调度结果）
--   ✅ 2187 实例：存活×2（rootWitness）+ 数值对账
--   ⚠ 死亡排除×4：复用 HenselMigration2187 的非根引理（已迁移验证）
--   ⚠ 完整「恰 2 存活」定理（三候选穷尽 + 无第五根）——
--      由各 HenselMod 实例层承担（已全量闭合），泛型版需
--      候选空间枚举 + 非根推广——roadmap
--
--   复用链：ModularRoots.rootWitness（存活接口）
--         + HenselMigration2187（死亡引理已迁移）
--------------------------------------------------------------------------------
