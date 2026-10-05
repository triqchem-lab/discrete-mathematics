{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.FixedPointQ16
-- 律算本源线 S1b：Q16 定点算术——zhonglvClosure 的实现前提
--
-- 数学背景：定点数 Q16 表示真值 v 为 v × 2¹⁶ 的整数。
--   2¹⁶ = 65536 = CLOSURE_DEN（SunyiBase 的闭合比分母）。
--   zhonglvClosure：acc' = (acc × 3¹¹) / 2¹⁶（仲吕→黄钟闭合操作）。
--   仲吕 30 × 177147 = 5314410，5314410 / 65536 = 81（整数除法）→ 黄钟 ✓
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.FixedPointQ16 where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _<_; _≤_; _/_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Algebra.SunyiBase
  using (CLOSURE_NUM; CLOSURE_DEN; SOVEREIGN_LCM; sun; yi; 仲吕不能自生黄钟)

--------------------------------------------------------------------------------
-- §1. Q16 类型与常数
--------------------------------------------------------------------------------

-- Q16 定点数：真值 = Q16值 / 65536
-- 用 ℕ 直接表示（宪法：禁浮点）
Q16 : Set
Q16 = ℕ

-- Q16 精度分母
Q16_DEN : ℕ
Q16_DEN = 65536

-- √3 的 Q16 floor 截断（数学精确：floor(√3 × 65536) = 113511）
SQRT3_Q16 : ℕ
SQRT3_Q16 = 113511

-- √3/2 的 Q16 floor 截断
SQRT3_HALF_Q16 : ℕ
SQRT3_HALF_Q16 = 56756

-- 2.0 的 Q16 表示
TWO_Q16 : ℕ
TWO_Q16 = 131072

--------------------------------------------------------------------------------
-- §2. zhonglvClosure——仲吕闭合操作
--
--   zhonglvClosure(acc) = (acc × 3¹¹) / 2¹⁶
--   = (acc × CLOSURE_NUM) / CLOSURE_DEN
--   = 仲吕→黄钟的定点算术闭合
--------------------------------------------------------------------------------

zhonglvClosure : ℕ → ℕ
zhonglvClosure acc = (acc * CLOSURE_NUM) / CLOSURE_DEN

--------------------------------------------------------------------------------
-- §3. 闭合验证
--------------------------------------------------------------------------------

-- 仲吕→黄钟闭合：zhonglvClosure(30) = 30 × 177147 / 65536 = 5314410 / 65536 = 81
zhonglv-30-closes : zhonglvClosure 30 ≡ 81
zhonglv-30-closes = refl

-- 黄钟自检验：zhonglvClosure(81) = 81 × 177147 / 65536 = 14348907 / 65536 ≈ 218（非 81——黄钟不是闭合点）
-- 闭合只发生在仲吕→黄钟（单向往返，非循环）

-- SOVEREIGN_LCM 引用验证
lcm-check : SOVEREIGN_LCM ≡ CLOSURE_NUM * CLOSURE_DEN
lcm-check = refl

lcm-value : SOVEREIGN_LCM ≡ 11609505792
lcm-value = refl

-- Q16 分母与闭合比分母一致
q16-den-is-closure-den : Q16_DEN ≡ CLOSURE_DEN
q16-den-is-closure-den = refl
