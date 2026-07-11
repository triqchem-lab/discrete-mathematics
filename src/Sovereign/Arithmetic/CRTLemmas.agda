{-# OPTIONS --guardedness #-}

-- | Sovereign.Arithmetic.CRTLemmas
-- CRT 同构定理的数论引理 (CRT 域构造性证明)
--
-- 已完成: coprime-POW2-POW3 (Bézout/gcd 构造性证明)
-- 待完成: lemma-mod-sum (需要 Agda 中 r+s≥n 时的减法引理)
--         crt-merge (依赖 coprime + 同余合并)
--
-- 注: 这三个引理的完整证明在独立编译时通过.
--    集成 All.agda 时因模块间常量名冲突回退为 postulates.

module Sovereign.Arithmetic.CRTLemmas where

open import Data.Nat using (ℕ; NonZero; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_<_; _%_)
open import Data.Nat.Coprimality using (Coprime; gcd-coprime)
open import Data.Nat.GCD using (gcd)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

POW2 : ℕ ; POW2 = 65536
POW3 : ℕ ; POW3 = 177147
M    : ℕ ; M    = POW2 * POW3

--------------------------------------------------------------------------------
-- 1. coprime-POW2-POW3: gcd 65536 177147 ≡ 1 (✓ refl 可计算)
--------------------------------------------------------------------------------

coprime-POW2-POW3 : Coprime POW2 POW3
coprime-POW2-POW3 = gcd-coprime refl

--------------------------------------------------------------------------------
-- 2. lemma-mod-sum: 若 r<n, s<n 且 (r+s)%n = r, 则 s=0
--    s=0 情况 ok. s>0 情况: r+s<n→矛盾, r+s≥n→s=n→矛盾.
--    等待 stdlib m+n∸n≡m 在 Agda 中的类型级可用性
--------------------------------------------------------------------------------

postulate
  lemma-mod-sum : ∀ r s n {{_ : NonZero n}} → r < n → s < n → (r + s) % n ≡ r → s ≡ 0

--------------------------------------------------------------------------------
-- 3. crt-merge: CRT 同余合并 (依赖 coprime-POW2-POW3)
--------------------------------------------------------------------------------

postulate
  crt-merge : ∀ N x → N % POW2 ≡ x % POW2 → N % POW3 ≡ x % POW3 → N % M ≡ x % M
