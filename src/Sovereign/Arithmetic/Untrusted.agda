{-# OPTIONS --guardedness #-}

-- | Sovereign.Arithmetic.Untrusted
-- 隔离层：集中管理未信任的外部算术引理 (Data.Nat.*)
--
-- 宪法原则：
-- 1. 所有外部算术引理初始信任度为 0 (UNTRUSTED)。
-- 2. 禁止核心宪法模块直接引用外部标准库。
-- 3. 必须通过此隔离层访问，以便在阶段 2 替换为高维几何重新证明的版本。

module Sovereign.Arithmetic.Untrusted where

-- ⚠️ UNTRUSTED: 基于连续统算术，需在高维几何中重新证明
-- 包含：模运算分配律 (+-mod), 乘法模零律 (m*n%m≡0), 模小于除数 (mod-<) 等
open import Data.Nat.Properties public 

-- ⚠️ UNTRUSTED: 除法 - 模分解唯一性，需在 Base-3 编码中验证
open import Data.Nat.DivMod public 

-- 备注：
-- 阶段 2 计划：
-- 1. 在 Sovereign.RootMath.Arithmetic 中重新实现上述引理。
-- 2. 基于 GF(3) 格点拓扑证明。
-- 3. 替换此模块的内容。
