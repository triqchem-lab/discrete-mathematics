{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.CosmologyDiscrete
-- C41: 离散宇宙学 — 4320 容量 + 729 格点
--
-- 核心命题:
--   1. 4320 全息容量: 729×6 - 54 = 4320 (引用 yao-4320)
--   2. 729 格点: T⁶ = GF(3)⁶ 的基数 (引用 T6 相关)
--
-- 0 postulate, 穷举法优先

module Sovereign.Applied.CosmologyDiscrete where

open import Data.Nat using (ℕ; _+_; _*_; _∸_; _^_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.BurnsideT6
  using (yao-4320; independent-info-from-yao;
         4320D-factor-decomposition; Merkaba-24; Water-36; Wuxing-5;
         orbit-sizes-sum-729)

--------------------------------------------------------------------------------
-- §1. 4320 全息容量
--
-- 宇宙学核心问题: 宇宙的信息容量是多少?
-- 离散宇宙学: 容量 = 4320D (全息维度)
--
-- 两条路径到 4320:
--   路径 1: 24(梅尔卡巴) × 36(水态谐波) × 5(五行) = 4320
--   路径 2: 729×6 - 54 = 4320 (裸爻变空间 - 规范群阶)
--
-- 引用: yao-4320 (BurnsideT6.agda)
--------------------------------------------------------------------------------

-- 4320 容量: 爻变路径 (729×6 - 54)
cosmology-capacity-4320 : independent-info-from-yao ≡ 4320
cosmology-capacity-4320 = yao-4320

-- 4320 容量: 分解路径 (24×36×5)
cosmology-factor-4320 : Merkaba-24 * Water-36 * Wuxing-5 ≡ 4320
cosmology-factor-4320 = 4320D-factor-decomposition

-- 两条路径一致
cosmology-both-paths : Merkaba-24 * Water-36 * Wuxing-5 ≡ independent-info-from-yao
cosmology-both-paths = refl

--------------------------------------------------------------------------------
-- §2. 729 格点: T⁶ 宇宙基底
--
-- T⁶ = GF(3)⁶ 有 729 个格点
-- 这是宇宙的"最小分辨率"——不存在更细的结构
--
-- 729 = 3⁶: 6 个维度, 每维 3 态
-- 格点群作用: G = (C₃)³ × C₂, |G| = 54
-- 轨道分解: 1×27 + 13×54 = 729 (群论闭包)
--------------------------------------------------------------------------------

-- 3⁶ = 729 (T⁶ 格点总数)
cosmology-t6-cardinality : 3 ^ 6 ≡ 729
cosmology-t6-cardinality = refl

-- 格点乘法验证
cosmology-729-product : 3 * 3 * 3 * 3 * 3 * 3 ≡ 729
cosmology-729-product = refl

-- 群论闭包: 轨道大小之和 = 729 (27×1 + 54×13 = 729)
cosmology-orbit-closure : 27 * 1 + 54 * 13 ≡ 729
cosmology-orbit-closure = orbit-sizes-sum-729

-- 规范群阶: 54 = 2 × 3³
cosmology-gauge-order : 2 * 3 * 3 * 3 ≡ 54
cosmology-gauge-order = refl

-- 裸空间: 729 × 6 = 4374
cosmology-bare-space : 729 * 6 ≡ 4374
cosmology-bare-space = refl

-- 物理自由度: 4374 - 54 = 4320
cosmology-physical-dof : 4374 ∸ 54 ≡ 4320
cosmology-physical-dof = refl

--------------------------------------------------------------------------------
-- §3. 4320 素因子分解验证 (穷举法)
--
-- 4320 = 2⁵ × 3³ × 5 = 32 × 27 × 5
-- 每个素因子对应一个物理对称性:
--   2⁵ = 32: 梅尔卡巴 24 的 2-幂骨架
--   3³ = 27: GF(3)³ 规范群的 3-幂阶
--   5¹ =  5: 五行循环群 C₅
--------------------------------------------------------------------------------

-- 4320 = 2 × 2160 (2-可除性)
factor-4320-2 : 4320 ≡ 2 * 2160
factor-4320-2 = refl

-- 4320 = 3 × 1440 (3-可除性)
factor-4320-3 : 4320 ≡ 3 * 1440
factor-4320-3 = refl

-- 4320 = 5 × 864 (5-可除性)
factor-4320-5 : 4320 ≡ 5 * 864
factor-4320-5 = refl

-- 4320 = 32 × 135 (2⁵ 与奇数部分分离)
factor-4320-full : 4320 ≡ 32 * 135
factor-4320-full = refl

-- 4320 = 2⁵ × 3³ × 5 (完全素因子分解)
factor-4320-prime : 4320 ≡ 2 ^ 5 * 3 ^ 3 * 5
factor-4320-prime = refl

-- 验证: 2⁵ = 32
factor-2pow5 : 2 ^ 5 ≡ 32
factor-2pow5 = refl

-- 验证: 3³ = 27
factor-3pow3 : 3 ^ 3 ≡ 27
factor-3pow3 = refl
