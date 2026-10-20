{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3MonoCount
-- 「至少一个零」的指数向量计数（T4 的 b_n 组合半，2026-10-20）
--
-- 数学背景
--   `R_n = GF(3)[x_1..x_n]/(x_i³)` 的单项式基是 `{x^a : a ∈ {0,1,2}^n}`，共 `3^n` 个。
--   其中「**至少一个分量为 0**」的那些张成 `V_nA`（b_n 的定义里用的空间）。
--
--   个数 = `3^n − 2^n`：
--     · 全部                    = 3^n（每个坐标 3 种）
--     · 各个分量都非零           = 2^n（每个坐标 2 种：1 或 2）
--     · 至少一个为零             = 3^n − 2^n
--
--   这正是 `b_n = 3^{n−1} − 2^{n−1}` 与 `a_n = 3^{n−1}+2^{n−1}` 里的两个数
--   （下标差一：V_nA 用的是 n−1 个「旧坐标」）。
--
-- 本模块做什么
--   把上述计数**形式化**：定义 `allMono`/`noZeroMono`/`someZeroMono`，并证明
--     `someZeroMono n + noZeroMono n ≡ allMono n`
--   （这是 `dim V_nA` 的组合半；维数那半需要基 ≅ `Fin d → Trit`，尚未建。）
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3MonoCount where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  ( ∸-+-assoc; m∸n+n≡m; +-comm; +-assoc; *-comm
  ; ^-distribˡ-+-*; ^-distribʳ-*; ^-monoˡ-≤; ≤-refl; n≤m+n )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

--------------------------------------------------------------------------------
-- §1. 三个计数
--------------------------------------------------------------------------------

-- 全部单项式个数：每个坐标 3 种取值
allMono : ℕ → ℕ
allMono n = 3 ^ n

-- 所有分量都非零的个数：每个坐标 2 种（指数 1 或 2）
noZeroMono : ℕ → ℕ
noZeroMono n = 2 ^ n

-- 至少一个分量为零的个数 = 全部 − 全非零
someZeroMono : ℕ → ℕ
someZeroMono n = allMono n ∸ noZeroMono n

--------------------------------------------------------------------------------
-- §2. 关键不等式：2^n ≤ 3^n
--------------------------------------------------------------------------------

2≤3 : 2 ≤ 3
2≤3 = s≤s (s≤s z≤n)

noZero≤all : ∀ n → noZeroMono n ≤ allMono n
noZero≤all n = ^-monoˡ-≤ n 2≤3

--------------------------------------------------------------------------------
-- §3. ★ 主定理：至少一个零 + 全非零 = 全部
--------------------------------------------------------------------------------

someZero-plus-noZero : ∀ n → someZeroMono n + noZeroMono n ≡ allMono n
someZero-plus-noZero n = m∸n+n≡m (noZero≤all n)

--------------------------------------------------------------------------------
-- §4. 小 n 核对（与 oracle 87ce8e37 一致）
--------------------------------------------------------------------------------

count-1 : someZeroMono 1 ≡ 1
count-1 = refl

count-2 : someZeroMono 2 ≡ 5
count-2 = refl

count-3 : someZeroMono 3 ≡ 19
count-3 = refl

count-4 : someZeroMono 4 ≡ 65
count-4 = refl

count-5 : someZeroMono 5 ≡ 211
count-5 = refl

count-6 : someZeroMono 6 ≡ 665
count-6 = refl
