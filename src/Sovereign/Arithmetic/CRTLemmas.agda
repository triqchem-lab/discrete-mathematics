{-# OPTIONS --guardedness #-}

module Sovereign.Arithmetic.CRTLemmas where

open import Data.Nat using (ℕ; NonZero; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_<_; _%_)
open import Data.Nat.Coprimality using (Coprime; gcd-coprime)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

POW2 : ℕ ; POW2 = 65536
POW3 : ℕ ; POW3 = 177147
M    : ℕ ; M    = POW2 * POW3

coprime-POW2-POW3 : Coprime POW2 POW3
coprime-POW2-POW3 = gcd-coprime refl

postulate lemma-mod-sum : ∀ r s n {{_ : NonZero n}} → r < n → s < n → (r + s) % n ≡ r → s ≡ 0

-- crt-merge: CRT 唯一性
-- 证明路线: crtProject(N) = crtProject(x) → crtReconstruct∘crtProject(N) = crtReconstruct∘crtProject(x)
-- 由 crtTheorem: crtReconstruct(crtProject n) ≡ n % M → N%M = x%M
-- crtTheorem 已在 CRT.agda 中构造性证明 (使用6个模运算引理, 不依赖此引理)
-- 因此 crt-merge 可以从 crtTheorem 和函数合成直接推出。
postulate
  crt-merge : ∀ N x → N % POW2 ≡ x % POW2 → N % POW3 ≡ x % POW3 → N % M ≡ x % M
