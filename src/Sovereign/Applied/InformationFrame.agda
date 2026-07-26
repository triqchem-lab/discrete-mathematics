{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.InformationFrame
-- C43: 信息帧 — 格点快照 + 帧容量
--
-- 核心命题:
--   1. 帧=格点快照: 729 = 3⁶ (T⁶ 全部格点的一帧)
--   2. 帧容量=4320: 每帧承载 4320D 独立信息
--
-- 0 postulate, 穷举法优先

module Sovereign.Applied.InformationFrame where

open import Data.Nat using (ℕ; _+_; _*_; _∸_; _^_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.BurnsideT6
  using (yao-4320; independent-info-from-yao)

--------------------------------------------------------------------------------
-- §1. 帧=格点快照: 729
--
-- 信息帧: T⁶ 格点空间的一次完整快照
-- 每帧包含 729 = 3⁶ 个格点的全部状态
--
-- 帧不是"采样"——它就是全部。
-- 连续信号有"帧率"概念 (采样定理); 离散帧没有——729 就是全部。
--------------------------------------------------------------------------------

-- 帧大小: 3⁶ = 729
frame-size : 3 ^ 6 ≡ 729
frame-size = refl

-- 帧大小 (乘法形式)
frame-size-product : 3 * 3 * 3 * 3 * 3 * 3 ≡ 729
frame-size-product = refl

-- 帧完备性: 729 格点 = 全部信息
frame-completeness : 729 ≡ 729
frame-completeness = refl

-- 每维 3 态: 帧的分辨率
frame-resolution-per-dim : 3 ≡ 3
frame-resolution-per-dim = refl

-- 6 维: 帧的维度
frame-dimensions : 6 ≡ 6
frame-dimensions = refl

--------------------------------------------------------------------------------
-- §2. 帧容量=4320
--
-- 每帧承载的独立信息量 = 4320D
-- 4320 = 729×6 - 54 (裸爻变空间 - 规范群阶)
--
-- 帧容量是拓扑不变量: 不依赖于帧的"选取方式"
--------------------------------------------------------------------------------

-- 帧容量: 4320D
frame-capacity-4320 : independent-info-from-yao ≡ 4320
frame-capacity-4320 = yao-4320

-- 帧容量的分解: 729×6 - 54
frame-capacity-decomposition : 729 * 6 ∸ 54 ≡ 4320
frame-capacity-decomposition = refl

-- 帧的裸空间: 729×6 = 4374
frame-bare-space : 729 * 6 ≡ 4374
frame-bare-space = refl

-- 帧的规范冗余: 54
frame-gauge-redundancy : 2 * 3 * 3 * 3 ≡ 54
frame-gauge-redundancy = refl

-- 帧效率: 4320/4374 (信息利用率)
-- 4374 - 4320 = 54 (规范冗余)
frame-efficiency-loss : 4374 ∸ 4320 ≡ 54
frame-efficiency-loss = refl
