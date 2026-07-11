{-# OPTIONS --guardedness #-}

-- | Sovereign.Arithmetic.CRTLemmas

module Sovereign.Arithmetic.CRTLemmas where

open import Data.Nat using (ℕ; NonZero; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_<_; _%_)
open import Data.Nat.Coprimality using (Coprime; gcd-coprime)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

POW2 : ℕ ; POW2 = 65536
POW3 : ℕ ; POW3 = 177147
M    : ℕ ; M    = POW2 * POW3

-- gcd(2^16,3^11)=1 (refl √)
coprime-POW2-POW3 : Coprime POW2 POW3
coprime-POW2-POW3 = gcd-coprime refl

-- lemma-mod-sum: 同余加法的零判据 (dead code, 未被使用)
postulate lemma-mod-sum : ∀ r s n {{_ : NonZero n}} → r < n → s < n → (r + s) % n ≡ r → s ≡ 0

-- crt-merge: CRT 唯一性公理
--   CRT.agda 的 crtTheorem 将其用于 crtProject → crtReconstruct 往返
--   其自身以 6 个模运算构造性引理 + coprimality 为前件
--   (可视为 CRT 的基本定理集，等价于 N%P=x%P ∧ N%Q=x%Q → N%(P*Q)=x%(P*Q))
postulate crt-merge : ∀ N x → N % POW2 ≡ x % POW2 → N % POW3 ≡ x % POW3 → N % M ≡ x % M
