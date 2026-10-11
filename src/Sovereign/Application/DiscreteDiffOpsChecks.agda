{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteDiffOpsChecks
-- DiscreteDiffOps 的跨域实例核对件汇（波 2-C 检查件外移）。
--
-- 数学背景：离散分部积分 1D 形（Σφ·Δψ 对称式）与差分求和归零的「定理命名面」——
-- 原居 Analysis/IntegrationByParts §1（具名委托），属「定理模块调实例核对」型错位边；
-- 按波 2-C 检查件外移模式迁至 Physics 侧独立检查件模块（委托目标同层，方向合法）。
--
-- 核心原则：
--   1. 本模块只承载委托/核对面（wrapper = 上游定理的命名引用），不新增数学内容；
--   2. Analysis/IntegrationByParts 保留自足 Abel 全形（§5/§6），零 Physics 依赖；
--   3. 波 2-C 验收：断链=0（原消费者零——grep 实证）。
--
-- 包含：integration-by-parts-theorem（委托对）｜diff-sum-zero（委托对）

module Sovereign.Physics.DiscreteDiffOpsChecks where

open import Data.Fin using (Fin) renaming (zero to fz)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Sovereign.Application.DiscreteDiffOps
  using (sum-forward; sum-backward; diff-sum;
         integration-by-parts-1d; integration-by-parts-zero)

---------------------------------------------------------------------------------
-- §1. 分部积分委托对（自 Analysis/IntegrationByParts §1 迁入——波 2-C）
---------------------------------------------------------------------------------

-- 分部积分定理 (L2 全称)：委托 DiscreteDiffOps.integration-by-parts-1d
integration-by-parts-theorem : ∀ φ ψ →
  sum-forward φ ψ ≡ sum-backward φ ψ
integration-by-parts-theorem = integration-by-parts-1d

-- 差分求和为零定理 (L2 全称)：委托 DiscreteDiffOps.integration-by-parts-zero
diff-sum-zero : ∀ φ ψ → diff-sum φ ψ ≡ fz
diff-sum-zero = integration-by-parts-zero
