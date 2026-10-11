{-# OPTIONS --rewriting --cubical --guardedness #-}

-- | Sovereign.HoTT.DiscreteCubical
-- 隔离层：集中管理未信任的 Cubical Agda 基础库
--
-- 宪法原则：
-- 1. Cubical.Foundations.Prelude 假设连续同伦类型论，初始信任度 0。
-- 2. 禁止 HoTT 模块直接引用外部 Cubical 库。
-- 3. 必须通过此隔离层访问，以便在阶段 2 替换为离散版本。
--
-- 核心原则：
--   1. 隔离层只做重导出（public import），零定义零证明
--   2. 每个重导出带 UNTRUSTED 标注与离散化待办
--
-- 包含：Prelude / Equiv / Function / Core.Primitives 四路重导出


module Sovereign.HoTT.DiscreteCubical where

-- ② 导入区（重导出，分组按信任面标注）

-- ⚠️ UNTRUSTED: 连续 Path 类型，可能与 T6 离散环面冲突
open import Cubical.Foundations.Prelude public

-- ⚠️ UNTRUSTED: 连续等价性，需离散化
open import Cubical.Foundations.Equiv public

-- ⚠️ UNTRUSTED: 高等组合子
-- NOTE: HComp not available in this cubical version
-- open import Cubical.Foundations.HComp public

-- ⚠️ UNTRUSTED: 函数扩展性 (FunExt) 在离散空间可能不成立
open import Cubical.Foundations.Function public

-- ⚠️ UNTRUSTED: 核心 Cubical 库
-- NOTE: Cubical.Core.Everything not available, importing what we need directly
open import Cubical.Core.Primitives public

-- ③-⑥ N/A（隔离层：零定义/零引理/零组合/零核对——本模块即「导入区」本身）

-- 备注：
-- 阶段 2 计划：
-- 1. 定义 Sovereign.HoTT.DiscreteCubical.DiscretePrelude
-- 2. 重新定义 Path 为离散连接 (Discrete Connection)。
-- 3. 替换此模块的内容。
