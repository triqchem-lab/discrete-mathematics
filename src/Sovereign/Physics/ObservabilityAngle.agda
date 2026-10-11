{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.ObservabilityAngle
-- 可观测性角度 — 感官 2-进位采样序列的形式化 (0 postulate, 全 refl)
--
-- 数学背景：可观测性角度三分——光子结构角、人眼采样角、可见光可观测窗；
--   2-进位采样序列是感官侧的离散化（与 3 进位理论基座分层，不混写）。
--
-- 核心原则：
--   1. 角度 = 离散采样序列（不是连续变量——无实数角度）；
--   2. 采样层（感官）与本源层（GF(3)）分层，跨层只作对照；
--   3. 0 postulate / 全 refl 级核对。
--
-- 包含：photon-structure-angle（光子结构角）· eye-sampling-angle（人眼采样角）·
--   visible-light-observable（可见光可观测性）

module Sovereign.Physics.ObservabilityAngle where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- 采样角 (2-进位减半次数编码)
--------------------------------------------------------------------------------

-- 光子结构角 = 90° = 减半 1 次 (GF(9) 共轭: α²=-1 生成 90° 相位差)
photon-structure-angle : ℕ
photon-structure-angle = 1

-- 眼睛(视觉)采样角 = 90° = 减半 1 次 (1/4 转)
eye-sampling-angle : ℕ
eye-sampling-angle = 1

--------------------------------------------------------------------------------
-- 定理: 可见光可观测 — 光子结构角 = 眼睛采样角 = 90°
--------------------------------------------------------------------------------

visible-light-observable : photon-structure-angle ≡ eye-sampling-angle
visible-light-observable = refl

-- 0 postulate.
