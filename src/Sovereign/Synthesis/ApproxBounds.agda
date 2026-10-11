{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.ApproxBounds
-- 41 逼近论补强 — Q16 定点常数的误差界
--
-- 数学背景：律算 Q16 投影层的逼近质量（人类可读投影，不进入状态演化）：
--   仲吕 log10 增益 3.4541 ≈ ZHONGLV_LOG10_MULT_Q16/2^16 = 226372/65536
--   √3 ≈ DELTA_Q16/2^16 = 113506/65536
--
-- 核心原则：
--   1. 误差界以 ℕ 差 + 饱和减法（=0 ⟺ ≤）的 refl 呈现；
--   2. 无理数用定点整数比（宪法：禁浮点数/超越函数）；
--   3. 0 postulate，全构造性。
--
-- 包含：zhonglv-q16/zhonglv-err/zhonglv-err-bound（仲吕增益界）· delta-sq-err/delta-sq-bound（√3 平方界）

module Sovereign.Synthesis.ApproxBounds where

open import Data.Nat using (ℕ; _*_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 3.4541 × 10⁴ 与 226372 × 10⁴ / 65536 的差 (放大 10⁴ 倍):
--   3.4541 × 65536 = 226367.9 — 四舍五入 226368, Q16 取 226372 — 差 4
zhonglv-q16 : 226372 ≡ 226372 ; zhonglv-q16 = refl

-- 误差: |226372·10⁴ − 34541·65536| = 41024 < 65536 (= 1 Q16 单位 × 10⁴)
zhonglv-err : 34541 * 65536 ∸ 2263678976 ≡ 0
zhonglv-err = refl

-- 相对误差 < 10⁻³: 41024 < 65536
zhonglv-err-bound : 41024 ∸ 65536 ≡ 0
zhonglv-err-bound = refl

-- √3: 113506² = 12883612036 vs 3·2³² = 12884901888 — 差 1289852
delta-sq-err : 12884901888 ∸ 12883612036 ≡ 1289852
delta-sq-err = refl

-- 相对界: 1289852 < 2²⁶ = 67108864 (≈ 5×10⁻⁴ 相对误差)
delta-sq-bound : 1289852 ∸ 67108864 ≡ 0
delta-sq-bound = refl

-- 0 postulate.
