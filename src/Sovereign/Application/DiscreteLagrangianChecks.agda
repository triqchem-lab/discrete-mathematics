{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.DiscreteLagrangianChecks
-- DiscreteLagrangian 的跨域实例核对件汇（波 2-C 检查件外移）。
--
-- 数学背景：Euler-Lagrange 等价形（临界点 ⟺ EL 方程）的「定理命名面」——
-- 原居 Analysis/CalculusOfVariations §3/§4（具名委托对），属「定理模块调实例核对」型；
-- 迁至 Physics 侧独立检查件模块（委托目标同层）。CoV 保留自足 §1/§2（作用量/变分导数）。
--
-- 核心原则：
--   1. 本模块只承载委托/核对面，不新增数学内容；
--   2. 零外部消费者（grep 实证）——迁移零断链。
--
-- 包含：el-equivalence（双向委托对）｜el-constant（常值 EL）

module Sovereign.Application.DiscreteLagrangianChecks where

open import Data.Fin using (Fin) renaming (zero to fz)
open import Data.Product using (_×_; _,_)
open import Sovereign.Application.DiscreteLagrangian
  using (satisfies-EL; is-critical; critical-to-el; el-to-critical; el-const)

---------------------------------------------------------------------------------
-- §1. EL 等价委托对（自 Analysis/CalculusOfVariations 迁入——波 2-C）
---------------------------------------------------------------------------------

-- 变分原理等价形 (L2 全称)：临界点 ⟺ EL——委托 DiscreteLagrangian 双向引理
el-equivalence : ∀ φ i →
  (is-critical φ i → satisfies-EL φ i)
  × (satisfies-EL φ i → is-critical φ i)
el-equivalence φ i = critical-to-el φ i , el-to-critical φ i

-- 常值场 EL (L2 全称)：委托 DiscreteLagrangian.el-const
el-constant : ∀ i → satisfies-EL (λ _ → fz) i
el-constant = el-const
