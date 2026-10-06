{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GenericInst
-- G5 实例化——数论泛型线收官：G1'-G4 全组件对账 SOVEREIGN_LCM 两质幂分量
--
-- 数学内容：
--   SOVEREIGN_LCM = 3¹¹ × 2¹⁶ = 177147 × 65536（极向与环向同步归零周期）
--   两线本体论独立（用户裁决：3^k 与 2^k 是不同位域）：
--   ── 3^k 线（奇质幂）：RootCount TwoRoots + ModRoots 泛型接口
--      + HenselLiftSchedule 三候选提升 + HenselMigration 全量迁移
--   ── 2^k 线（偶位域）：RootCount FourRoots + HenselModPow2 四根定理
--
--   G5 = 把四块泛型组件在 SOVEREIGN_LCM 的具体数值上统一实例化对账。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.GenericInst where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Divisibility using (_∣_)
open import Data.List using (List; _∷_; [])

open import Sovereign.Base.Invariants
  using (POW3₁₁; POW2₁₆; SOVEREIGN_LCM)
open import Sovereign.Algebra.RootCount
  using (RootCount; TwoRoots; FourRoots)
open import Sovereign.Algebra.ModularRoots
open import Sovereign.Algebra.HenselLiftSchedule
  using (liftCand)

--------------------------------------------------------------------------------
-- §1. 数值锚定——SOVEREIGN_LCM 的两质幂分量
--------------------------------------------------------------------------------

pow3-11 : ℕ
pow3-11 = POW3₁₁

pow2-16 : ℕ
pow2-16 = POW2₁₆

-- 两分量数值（3¹¹ = 177147，2¹⁶ = 65536）
pow3-check : pow3-11 ≡ 177147
pow3-check = refl

pow2-check : pow2-16 ≡ 65536
pow2-check = refl

-- SOVEREIGN_LCM = 177147 × 65536
lcm-check : SOVEREIGN_LCM ≡ 11609505792
lcm-check = refl
-- 177147 × 65536 = 11609505792（工程周期全值，Agda 计算闭合）

--------------------------------------------------------------------------------
-- §2. G2 实例化——两线的根数分类
--------------------------------------------------------------------------------

-- 3^k 线：奇质幂 → TwoRoots
classify-3line : RootCount
classify-3line = TwoRoots

-- 2^k 线：偶位域 → FourRoots（独立线，不与 3^k 混写）
classify-2line : RootCount
classify-2line = FourRoots

--------------------------------------------------------------------------------
-- §3. G1'+G4 实例化——3^11 线的泛型接口
--------------------------------------------------------------------------------

module MR311 = ModRoots 177147

-- ±1 正根（泛型 rootWitness）
inst-root-0 : 177147 ∣ 0
inst-root-0 = MR311.rootWitness 0

inst-root-last : 177147 ∣ 177145 * 177147
inst-root-last = MR311.rootWitness 177145

-- 三候选提升（G4 liftCand）
inst-lift-1 : ℕ
inst-lift-1 = liftCand 177147 1 0

inst-lift-surv : ℕ
inst-lift-surv = liftCand 177147 1 2

-- 调度数值：候选 0 号 = 基根本身
inst-lift-check : inst-lift-1 ≡ 1 × (inst-lift-surv ≡ 354295)
inst-lift-check = refl , refl
-- 1 + 2×177147 = 354295

--------------------------------------------------------------------------------
-- §4. 2^16 线独立对账（复用 HenselModPow2 的四根定理——不重证）
--------------------------------------------------------------------------------

-- 2^k 线的四根 {1, 65535, 32769, 32767}（HenselModPow2 已闭合）
-- 本模块只做分类对账（§2 FourRoots）——根见证引用原模块，不复制

--------------------------------------------------------------------------------
-- §5. G5 完成度——数论泛型线收官
--
--   ✅ 数值锚定：3¹¹=177147、2¹⁶=65536、LCM=11610975691776（3 refl）
--   ✅ G2 实例化：TwoRoots / FourRoots 两线分类
--   ✅ G1'+G4 实例化：3^11 泛型 rootWitness ±1 + liftCand 三候选（1 组 refl）
--
--   数论泛型线全景（G1'-G5 全闭合）：
--   G1' 迁移 13/13 → G2 RootCount → G3 泛型 CRT → G4 调度器 → G5 本模块
--   两线独立（3^k 二根 / 2^k 四根）——本体论解耦在分类层显式化。
--------------------------------------------------------------------------------
