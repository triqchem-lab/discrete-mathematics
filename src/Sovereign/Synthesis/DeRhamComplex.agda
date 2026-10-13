{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.DeRhamComplex
-- 离散 de Rham 复形 (L3 深层证明)
--
-- 核心命题:
--   离散 de Rham 复形 d²=0 的 GF(3) 版本:
--   div∘curl = 0, curl∘grad = 0, 即 d²=0 在离散格点上成立。
--
-- 证明策略:
--   §1 离散微分形式 (0-形式=标量场, 1-形式=向量场, 2-形式=标量场)
--   §2 外微分算子 (grad, curl, div)
--   §3 d²=0 恒等式 (div∘curl=0, curl∘grad=0)
--   §4 de Rham 复形结构 (链复形)
--
-- 全部 0 postulate, GF(3) 穷举 refl + 符号推理。

module Sovereign.Synthesis.DeRhamComplex where

-- [波 2-C 检查件外移] 本模块全部实例核对 wrapper 已迁
--   Sovereign.Application.DiscreteEMIdentityChecks（curl-grad-zero-full / div-curl-zero-full / d-squared-zero / de-rham-complex）——
--   委托目标（DiscreteEMField3D/DiscreteEMCore 恒等式）同层，方向合法；
--   本模块保留为结构性占位（§1-§4 数学背景注释见 git 历史 4aa248b 前版）。
-- 零 Physics 依赖 ✓（波 2-C 断链判据）
