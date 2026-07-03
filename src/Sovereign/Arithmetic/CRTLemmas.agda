{-# OPTIONS --guardedness #-}

-- | Sovereign.Arithmetic.CRTLemmas
-- CRT 同构定理的数论引理 (内部模块, 非公开)
--
-- 引理:
--   1. coprime-POW2-POW3: gcd(65536, 177147) = 1
--   2. lemma-mod-sum: 模运算辅助引理
--   3. crt-merge: N%m1=x%m1 ∧ N%m2=x%m2 → N%M=x%M
--
-- 注: 这些引理的证明纲要见文档和注释.
--   完整形式化需要 ℤ 减法或商空间理论.

module Sovereign.Arithmetic.CRTLemmas where

open import Data.Nat using (ℕ; NonZero; _+_; _*_)
open import Data.Nat.Base using (_<_; _%_)
open import Data.Nat.Coprimality using (Coprime)
open import Relation.Binary.PropositionalEquality using (_≡_)

POW2 : ℕ ; POW2 = 65536
POW3 : ℕ ; POW3 = 177147
M    : ℕ ; M    = POW2 * POW3

postulate
  coprime-POW2-POW3 : Coprime POW2 POW3
  lemma-mod-sum : ∀ r s n {{_ : NonZero n}} → r < n → s < n → (r + s) % n ≡ r → s ≡ 0
  crt-merge : ∀ N x → N % POW2 ≡ x % POW2 → N % POW3 ≡ x % POW3 → N % M ≡ x % M
