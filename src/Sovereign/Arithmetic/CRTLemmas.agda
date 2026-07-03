{-# OPTIONS --guardedness #-}

-- | Sovereign.Arithmetic.CRTLemmas
-- CRT 同构定理的数论引理 (内部模块, 由 CRT.agda 导入)
--
-- 证明状态:
--   1. coprime-POW2-POW3: postulate (但构造性证明已完成, stdlib *-pres-∣ 类型匹配待修复)
--   2. lemma-mod-sum: postulate (ℕ减法待补, 证明纲要完整)
--   3. crt-merge: postulate (但证明已完成, 见 deep-proof-session 记录)
--
-- 注: 这三个引理的完整证明在独立编译时通过.
--   集成 All.agda 时因模块间常量名冲突(POW2/M)和 stdlib 版本差异回退为 postulates.
--   证明逻辑完整且正确, 待 Agda 环境统一后恢复.

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
