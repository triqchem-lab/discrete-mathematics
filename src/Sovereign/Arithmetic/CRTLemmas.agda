{-# OPTIONS --guardedness #-}

module Sovereign.Arithmetic.CRTLemmas where

open import Data.Nat using (ℕ; NonZero; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_<_; _%_)
open import Data.Nat.Coprimality using (Coprime; gcd-coprime)
open import Data.Nat.GCD using (gcd)
open import Data.Nat.DivMod using (m%n%n≡m%n; [m+kn]%n≡m%n)
open import Data.Nat.Properties using (*-comm; +-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

POW2 : ℕ ; POW2 = 65536
POW3 : ℕ ; POW3 = 177147
M    : ℕ ; M    = POW2 * POW3

-- 1. coprime: gcd 2^16 3^11 = 1 (refl)
coprime-POW2-POW3 : Coprime POW2 POW3
coprime-POW2-POW3 = gcd-coprime refl

-- 2. lemm-mod-sum: basic modular arithmetic (可对小 n refl 验证, 通用证明待 stdlib)
postulate
  lemma-mod-sum : ∀ r s n {{_ : NonZero n}} → r < n → s < n → (r + s) % n ≡ r → s ≡ 0

-- 3. crt-merge: CRT 唯一性 — 同余模互质因子 → 同余模乘积
--    证明: N ≡ x (mod POW2) → N-x = q*POW2; 同 POW3 → N-x = q'*POW3
--    由 coprime → N-x 是 M = POW2*POW3 的倍数 → N%M = x%M
--    需要 Data.Nat.Divisibility 的 |m*n 和 coprime|lcm 引理
postulate
  crt-merge : ∀ N x → N % POW2 ≡ x % POW2 → N % POW3 ≡ x % POW3 → N % M ≡ x % M
