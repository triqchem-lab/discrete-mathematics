{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.ModularRoots
-- 泛型系数代数框架 P1：模数参数化的根见证机件
--
-- 架构对齐：借鉴 Lean Mathlib 类型类层次 + hex-hensel 两阶段设计，
--   以 Agda 参数化模块实现。消除 17 个 HenselMod* 中 136 处非根排除的模式重复。
--
-- 数学内容：
--   NonRootWitness d k r b : 若 N = k·d + r 且 r < d，则 ¬(d ∣ N)
--   RootWitness d k        : d ∣ k·d（正根见证）
--
-- 设计原则（对齐外部实践）：
--   - 参数化模块（Agda 版 type-class）——路径 A
--   - refl 统一——N 与 k·d+r 的定义相等由字面量计算保证
--   - stdlib ∣m+n∣m⇒∣n 直接复用——G1 零重复
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.ModularRoots where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; _≤_; NonZero)
open import Data.Empty using (⊥)
open import Data.Nat.Divisibility
  using (_∣_; ∣m+n∣m⇒∣n; ∣⇒≤; n∣m*n)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Algebra.HenselLiftUniqueness using (≤<-asym; 1+<-trans)

--------------------------------------------------------------------------------
-- §1. 泛型模块：参数化模数 d
--------------------------------------------------------------------------------

module ModRoots (d : ℕ) where

  -- 泛型 step（∣m+n∣m⇒∣n 的 d-实例——stdlib 已有，此处仅暴露接口）
  ∣d-step : ∀ {m r : ℕ} → d ∣ (m + r) → d ∣ m → d ∣ r
  ∣d-step = ∣m+n∣m⇒∣n

  ------------------------------------------------------------------
  -- §1a. 正根见证：d ∣ k·d（对所有 k 成立——trivial）
  ------------------------------------------------------------------

  rootWitness : ∀ (k : ℕ) → d ∣ k * d
  rootWitness k = n∣m*n k {d}

  ------------------------------------------------------------------
  -- §1b. 非根排除：若 N = k·d + r 且 0 < r < d，则 ¬(d ∣ N)
  --
  --   模式来源：17 个 HenselMod* 中 136 处重复的泛型化。
  --   使用 refl 统一——Agda 字面量计算保证 N = k·d + r 定义性成立。
  --   bound 参数：满足 suc (bound + r) = d 的值（即 bound = d − r − 1）。
  ------------------------------------------------------------------

  nonRootWitness : ∀ (k r : ℕ) → ⦃ NonZero r ⦄ → r < d →
                   ¬ (d ∣ (k * d + r))
  nonRootWitness k r ⦃ nz ⦄ r<d h =
    ≤<-asym d r
      (∣⇒≤ (∣d-step h (rootWitness k)))
      r<d

--------------------------------------------------------------------------------
-- §2. 测试实例：mod 2187（从 HenselMod2187 迁移 2 条非根到泛型）
--   迁移验证：泛型版本产生与手写版本相同的结果
--------------------------------------------------------------------------------

module TestMod2187 = ModRoots 2187

-- x = 730 : x²-1 = 532899 = 531441 + 1458 = 243·2187 + 1458
-- 手写版（HenselMod2187）：
--   ¬2187∣532899 h = ≤<-asym 2187 1458
--     (∣⇒≤ (∣2187-step h (n∣m*n 243))) (1+<-trans 728 1458)
-- 泛型版：
test-nonRoot-730 : ¬ (2187 ∣ 532899)
test-nonRoot-730 = TestMod2187.nonRootWitness 243 1458 (1+<-trans 728 1458)

-- x = 1459 : x²-1 = 2128680 = 973·2187 + 729
test-nonRoot-1459 : ¬ (2187 ∣ 2128680)
test-nonRoot-1459 = TestMod2187.nonRootWitness 973 729 (1+<-trans 1457 729)

-- 正根对照
test-root-1 : 2187 ∣ 0
test-root-1 = TestMod2187.rootWitness 0

test-root-2186 : 2187 ∣ 4778595
test-root-2186 = TestMod2187.rootWitness 2185

--------------------------------------------------------------------------------
-- §3. 第二测试实例：mod 65536 = 2¹⁶（从 HenselModPow2 迁移）
--------------------------------------------------------------------------------

module TestMod65536 = ModRoots 65536

-- 四正根
test-pow2-root-1 : 65536 ∣ 0
test-pow2-root-1 = TestMod65536.rootWitness 0

test-pow2-root-32767 : 65536 ∣ 1073676288
test-pow2-root-32767 = TestMod65536.rootWitness 16383

test-pow2-root-32769 : 65536 ∣ 1073807360
test-pow2-root-32769 = TestMod65536.rootWitness 16385

test-pow2-root-65535 : 65536 ∣ 4294836224
test-pow2-root-65535 = TestMod65536.rootWitness 65534

-- 代表性非根
test-pow2-nonRoot-3 : ¬ (65536 ∣ 8)
test-pow2-nonRoot-3 = TestMod65536.nonRootWitness 0 8 (1+<-trans 65527 8)

test-pow2-nonRoot-16383 : ¬ (65536 ∣ 268402688)
test-pow2-nonRoot-16383 = TestMod65536.nonRootWitness 4095 32768 (1+<-trans 32767 32768)

--------------------------------------------------------------------------------
-- §4. 架构注记（对齐外部实践的路线图）
--
--   路径 B（备选）：record ModularRing (d : ℕ) 带 instance 参数
--     — 对齐 Lean Mathlib Semiring → Ring → Field 类型类层次
--     — 需要 Agda instance search 或 explicit dictionary passing
--     — 复杂度高，收益在长期（可与其他代数结构组合）
--
--   路径 A（当前）：参数化模块 ModRoots (d : ℕ)
--     — 轻量、直接、立即可用
--     — 消除 17 个模块中的非根/正根模式重复
--     — 后续 G2（根数分类）/G3（泛型 CRT）在此之上构建
--------------------------------------------------------------------------------
