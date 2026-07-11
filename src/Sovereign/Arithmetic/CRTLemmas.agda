{-# OPTIONS --guardedness #-}

-- | Sovereign.Arithmetic.CRTLemmas
-- CRT 域构造性证明
-- 完成: coprime-POW2-POW3 (gcd refl)
-- 待完成: lemma-mod-sum, crt-merge (需要 Data.Nat.Divisibility 整除链)

module Sovereign.Arithmetic.CRTLemmas where

open import Data.Nat using (ℕ; NonZero; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_<_; _%_)
open import Data.Nat.Coprimality using (Coprime; gcd-coprime)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

POW2 : ℕ ; POW2 = 65536
POW3 : ℕ ; POW3 = 177147
M    : ℕ ; M    = POW2 * POW3

-- proved: gcd(2^16, 3^11) = 1
coprime-POW2-POW3 : Coprime POW2 POW3
coprime-POW2-POW3 = gcd-coprime refl

-- lemma-mod-sum: auxiliary modular arithmetic lemma
-- Proof outline: s>0 → r+s>r. r+s<?n: r+s≡r (contra). r+s≥n:
--   r+s=n+k, k=r+s-n<r (since s<n). m%n = k%n = k (k<n) = r.
--   → s=n (contra s<n). Use [m+kn]%n≡m%n from stdlib.
postulate
  lemma-mod-sum : ∀ r s n {{_ : NonZero n}} → r < n → s < n → (r + s) % n ≡ r → s ≡ 0

-- crt-merge: CRT uniqueness — N≡x(mod POW2) ∧ N≡x(mod POW3) → N≡x(mod M)
-- Proof: Let d = |N-x|. POW2|d and POW3|d. Since coprime(POW2,POW3),
--   M = POW2*POW3 | d → N%M = x%M.
-- Needs: Data.Nat.Divisibility |m*n and coprime→lcm
postulate
  crt-merge : ∀ N x → N % POW2 ≡ x % POW2 → N % POW3 ≡ x % POW3 → N % M ≡ x % M
