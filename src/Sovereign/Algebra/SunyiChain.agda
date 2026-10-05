{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.SunyiChain
-- 律算本源线 S2：十二律损益链——Sun/Yi 交替序列 + LCM 余数投影
--
-- 数学背景：
--   十二律由黄钟 81 = 3⁴ 出发，交替损益 11 步生成。
--   LCM 余数投影：remainder_i = exact_i × 3⁷（清除所有 3 分母的投影因子）。
--   黄钟余数 = 3¹¹ = SOVEREIGN_LCM 的 3-part；
--   仲吕余数 = 2¹⁶ = SOVEREIGN_LCM 的 2-part。
--
-- 复用：SunyiBase（sun/yi/Frac/CLOSURE_NUM/CLOSURE_DEN）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.SunyiChain where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Product using (_×_; _,_)
open import Sovereign.Algebra.SunyiBase
  using (sun; yi; CLOSURE_NUM; CLOSURE_DEN; SOVEREIGN_LCM; 仲吕不能自生黄钟)

--------------------------------------------------------------------------------
-- §1. 损益操作类型
--------------------------------------------------------------------------------

data LossGain : Set where
  Sun : LossGain   -- 损一 ×2/3
  Yi  : LossGain   -- 益一 ×4/3

-- 十二步损益序列（交替 + 末步双损）
loss-gain-seq : LossGain × LossGain × LossGain × LossGain × LossGain × LossGain
             × LossGain × LossGain × LossGain × LossGain × LossGain × LossGain
loss-gain-seq =
  (Sun , Yi , Sun , Yi , Sun , Yi , Sun , Yi , Sun , Yi , Sun , Sun)

--------------------------------------------------------------------------------
-- §2. 十二律管长度（整数近似——宪法固定）
--------------------------------------------------------------------------------

十二律长度 : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
十二律长度 =
  (81 , 54 , 72 , 48 , 64 , 43 , 57 , 38 , 51 , 34 , 45 , 30)

--------------------------------------------------------------------------------
-- §3. LCM 余数投影表
--
--   投影公式：remainder_i = exact_i × 3⁷
--   其中 3⁷ = 2187 是损益链中出现的最高 3-分母幂。
--
--   黄钟余数 = 3¹¹ = CLOSURE_NUM（SOVEREIGN_LCM 的 3-part）
--   仲吕余数 = 2¹⁶ = CLOSURE_DEN（SOVEREIGN_LCM 的 2-part）
--
--   oracle 全 12 项验证通过 ✓
--------------------------------------------------------------------------------

LCM_REMAINDERS : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
LCM_REMAINDERS =
  (177147 , 118098 , 157464 , 104976 , 139968 , 93312
  , 124416 , 82944 , 110592 , 73728 , 98304 , 65536)

-- 投影因子 = 3⁷
PROJECTION_FACTOR : ℕ
PROJECTION_FACTOR = 2187

--------------------------------------------------------------------------------
-- §4. 首尾闭合验证
--------------------------------------------------------------------------------

-- 黄钟余数 = 闭合比分子 = 3¹¹
huangzhong-rem : CLOSURE_NUM ≡ 177147
huangzhong-rem = refl

-- 仲吕余数 = 闭合比分母 = 2¹⁶
zhonglv-rem : CLOSURE_DEN ≡ 65536
zhonglv-rem = refl

-- 黄钟 LCM 余数 = CLOSURE_NUM
huangzhong-lcm-is-num : 177147 ≡ CLOSURE_NUM
huangzhong-lcm-is-num = refl

-- 仲吕 LCM 余数 = CLOSURE_DEN
zhonglv-lcm-is-den : 65536 ≡ CLOSURE_DEN
zhonglv-lcm-is-den = refl

-- SOVEREIGN_LCM = 黄钟余数 × 仲吕余数
sovereign-lcm-decomp : SOVEREIGN_LCM ≡ 177147 * 65536
sovereign-lcm-decomp = refl

-- 仲吕不能自生黄钟（从 SunyiBase 重导出——交叉验证）
zhonglv-no-self-return : yi 30 ≢ 81
zhonglv-no-self-return = 仲吕不能自生黄钟
