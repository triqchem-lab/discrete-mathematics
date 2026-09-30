{-# OPTIONS --rewriting --guardedness #-}
-- | Sovereign.Problem.ABC.L1Rad
--
-- 完整范数核 rad（无平方因子核）：rad(n) = n 的互异质因子之积（rad 1 = 1）。
-- 最小质因子递归实现；终止以 fuel 递减保证（fuel 初值 n+1，实际步数 O(√n)）。
--
-- 数学背景：ABC 质量 q = c / rad(abc)；rad 是 L1 断层定理（L1Disjunction）
-- 的范数核观测，本模块把它从「参数 + 两值事实」升级为**可计算定义**。
--
-- 核心原则：
--   1. 三分支递归：n ≡ 1 → 1；k·k ≤ n 时试除 k（整除则取 k 一次并剥尽 k 的幂，
--      否则 k 递增）；1 < n < k·k 时余数 n 为质数，直接取 n。
--   2. 「剥尽 k 的幂」是无平方因子的关键：rad 4 ≡ 2（不是 4）、rad 480000 ≡ 30
--      （480000 = 2⁸·3·5⁴，幂次不进积）。
--   3. 模除走内置实现（BUILTIN NATDIVSUCAUX / NATMODSUCAUX，字面量除数一步
--      归约），避开朴素递归 mod 的 O(n) 展开；除数固定取 suc k 形态，
--      NonZero 实例由 nonZero 自动给出（附录 12 §3 的字面量除数纪律）。
--   4. 一切计算事实 refl 可核：rad 是**可计算**定义，由 Agda 内核求值裁决。
--
-- 包含：stripGo / radGo / rad / rad-1 / rad-120 / rad-480000 / 480000-factors
module Sovereign.Problem.ABC.L1Rad where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _/_; _≡ᵇ_; _≤ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- 1. 剥尽 k 的幂（去重的关键步骤：rad 4 ≡ 2 而非 4）
--------------------------------------------------------------------------------

-- stripGo f k n = n / k^m（m 为最大指数）；fuel 递减保证终止
stripGo : (fuel k n : ℕ) → ℕ
stripGo zero    k       n = n
stripGo (suc f) zero    n = n
stripGo (suc f) (suc k) n =
  if (n % suc k) ≡ᵇ 0 then stripGo f (suc k) (n / suc k) else n

--------------------------------------------------------------------------------
-- 2. rad 主循环（最小质因子候选 k 从 2 递增；fuel 递减保证终止）
--------------------------------------------------------------------------------

-- radGo f k n = n 的互异质因子之积中「≥ k 的候选」部分：
--   · n ≡ 1            → 1（无因子）
--   · k·k ≤ n          → 试除 k：整除则 k 进积一次并剥尽 k 的幂后 k 递增；
--                        不整除则 k 递增
--   · 1 < n < k·k      → n 为质数，直接进积
radGo : (fuel k n : ℕ) → ℕ
radGo zero    k       n = 1
radGo (suc f) zero    n = 1
radGo (suc f) (suc k) n =
  if (n ≡ᵇ 1) then 1
  else if ((suc k * suc k) ≤ᵇ n)
    then (if (n % suc k) ≡ᵇ 0
            then (suc k * radGo f (suc (suc k)) (stripGo f (suc k) n))
            else radGo f (suc (suc k)) n)
    else n

--------------------------------------------------------------------------------
-- 3. 完整范数核 rad（fuel 初值 = n+1）
--------------------------------------------------------------------------------

-- rad 0 约定取 0（ABC 三元组 abc > 0，不触达该分支）
rad : ℕ → ℕ
rad zero    = 0
rad (suc m) = radGo (suc (suc m)) 2 (suc m)

--------------------------------------------------------------------------------
-- 4. 计算事实（全部 refl 可核 = 内核求值裁决）
--------------------------------------------------------------------------------

rad-1 : rad 1 ≡ 1
rad-1 = refl

-- 见证对 w₁ = (3,5,8)：rad(3·5·8) = rad 120 = rad(2³·3·5) = 30
rad-120 : rad 120 ≡ 30
rad-120 = refl

-- 见证对 w₂ = (3,125,128)：rad(3·125·128) = rad 480000
--   480000 = 2⁸·3·5⁴ ⇒ rad = 2·3·5 = 30（与 rad 120 同值 ⇒ 观测盲区）
rad-480000 : rad 480000 ≡ 30
rad-480000 = refl

-- 质因数分解的算术核对（2⁸·3·5⁴ = 256·3·625 = 480000）
480000-factors : (256 * 3) * 625 ≡ 480000
480000-factors = refl

-- 小例：幂次去重的直接证据（rad 4 = 2，不是 4）
rad-4 : rad 4 ≡ 2
rad-4 = refl
