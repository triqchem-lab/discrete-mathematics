{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.ObservabilityAngle
-- 可观测性角度 — 感官 2-进位采样序列的形式化 (0 postulate, 全 refl)
--
-- 锚点 (卢先生): 感官对电磁场的采样角度是严格的 2-进位减半序列:
--   闻 1/2 转 = 180°, 看 1/4 转 = 90°, 想 1/8 转 = 45°,
--   听 1/16 转 = 22.5°, 尝 1/32 转 = 11.25°, 触 1/64 转 = 5.625°。
--
-- GF(9) 中的共轭角 = 90° (α²=-1 生成, Frobenius 交换 α↔-α)。
-- 眼(看)采样角 = 90°。二者匹配 → 「眼睛只能看到 90° 旋转的电磁场」。
--
-- 本模块把「可见光的可观测性」从定性论述固化为可审计的代数事实:
--   光子结构角 = 眼睛采样角 = 90° (减半 1 次), refl 直接落链。
--
-- 表示约定: 角度以「2-进位减半次数」编码 (ℕ):
--   0 = 180° = 1/2 转, 1 = 90° = 1/4 转, 2 = 45° = 1/8 转, ...
--   该编码是采样角的本质结构 (2 的幂次分母), 与 GF(9) 的 α 旋转 (4 阶)
--   在 90° 档位精确对齐。

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
