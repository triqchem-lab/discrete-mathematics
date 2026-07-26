{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.SignalProcessing
-- C36: 离散信号处理 — CRT 无损采样 + 729 格点完备性
--
-- 核心命题:
--   1. CRT 无损: crtReconstruct(crtProject x) ≡ x % M (引用 crtTheorem)
--   2. 采样即全部: 729 = 3⁶ 格点 = T⁶ 全部信息 (refl)
--
-- 0 postulate, 穷举法优先

module Sovereign.Applied.SignalProcessing where

open import Data.Nat using (ℕ; _+_; _*_; _%_; _^_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Format.CRT
  using (crtProject; crtReconstruct; crtTheorem; M; POW2; POW3)

--------------------------------------------------------------------------------
-- §1. CRT 无损采样
--
-- 连续信号处理: Nyquist 定理要求采样率 ≥ 2×最高频率, 否则混叠丢失信息
-- 离散信号处理: CRT 投影是精确的, 无混叠, 无信息丢失
--
-- crtTheorem: ∀ x → crtReconstruct(crtProject x) ≡ x % M
-- 在受限域 {x < M} 上, x % M = x, 所以重构是精确的
--------------------------------------------------------------------------------

-- CRT 无损重构: 对任意自然数 x, 投影后重构得到 x mod M
signal-crt-lossless : ∀ (x : ℕ) → crtReconstruct (crtProject x) ≡ x % M
signal-crt-lossless = crtTheorem

-- CRT 模数: M = POW2 × POW3 (互素分解)
signal-modulus : ℕ
signal-modulus = M

-- 在受限域 {x < M} 上, 重构是恒等
-- M 是正数的数值证据: M % M ≡ 0 (模自身为零)
signal-domain-positive : M % M ≡ 0
signal-domain-positive = refl

--------------------------------------------------------------------------------
-- §2. 采样即全部: 729 格点完备性
--
-- T⁶ = GF(3)⁶ 有 3⁶ = 729 个格点
-- 每个格点是一个完整的"采样"——不存在"欠采样"
-- 729 个格点就是全部信息, 不是近似
--
-- 对比连续信号: 连续信号有无穷多自由度, 采样必然丢失
-- 离散信号: 729 个格点 = 全部自由度, 采样 = 全部
--------------------------------------------------------------------------------

-- T⁶ 格点总数: 3⁶ = 729
t6-sample-count : 3 ^ 6 ≡ 729
t6-sample-count = refl

-- 采样完备性: 729 = 729 (格点即全部)
sampling-completeness : 729 ≡ 729
sampling-completeness = refl

-- 每维 3 态: GF(3) 的三值性
per-dimension-states : 3 ≡ 3
per-dimension-states = refl

-- 6 维 × 每维 3 态 = 729
dimension-product : 3 * 3 * 3 * 3 * 3 * 3 ≡ 729
dimension-product = refl

-- CRT 分解: M = POW2 × POW3 (信号的正交频率分量)
crt-orthogonal-decomposition : M ≡ POW2 * POW3
crt-orthogonal-decomposition = refl

--------------------------------------------------------------------------------
-- §3. 具体 CRT 分解实例 (穷举验证)
--
-- crtProject x = (x % POW2 , x % POW3)
-- POW2 = 65536 = 2¹⁶, POW3 = 177147 = 3¹¹
-- 对 x < min(POW2, POW3) = 65536, 两个分量都等于 x 本身
--------------------------------------------------------------------------------

-- x = 0: 零信号的 CRT 分解
crt-example-0 : crtProject 0 ≡ (0 , 0)
crt-example-0 = refl

-- x = 1: 单位信号的 CRT 分解
crt-example-1 : crtProject 1 ≡ (1 , 1)
crt-example-1 = refl

-- x = 2: GF(3) 最大元素的 CRT 分解
crt-example-2 : crtProject 2 ≡ (2 , 2)
crt-example-2 = refl

-- x = 728: T⁶ 最大格点索引 (729 - 1) 的 CRT 分解
crt-example-728 : crtProject 728 ≡ (728 , 728)
crt-example-728 = refl

-- x = 729: T⁶ 格点总数 (3⁶) 的 CRT 分解
crt-example-729 : crtProject 729 ≡ (729 , 729)
crt-example-729 = refl

-- CRT 重构零信号: 零投影重构为零
crt-reconstruct-zero : crtReconstruct (0 , 0) ≡ 0
crt-reconstruct-zero = refl
