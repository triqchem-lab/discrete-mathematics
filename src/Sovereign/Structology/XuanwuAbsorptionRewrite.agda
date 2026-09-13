{-# OPTIONS --rewriting --cubical --guardedness #-}

-- | Sovereign.Structology.XuanwuAbsorptionRewrite
-- 玄武吸收模块的 REWRITE 规则分离
--
-- 规则列表:
--   1. mod46k: (46*k)%46 = 0
--   2. div46k: (46*k)/46 = k
--   3. mod-a+598: (a+598)%46 = a%46  (598=13×46)

module Sovereign.Structology.XuanwuAbsorptionRewrite where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (div-helper; mod-helper; Nat; _*_; _+_)
open import Agda.Builtin.Equality.Rewrite

-- 环向缠绕数 46 的倍数自动化简规则
postulate
  mod46k : ∀ k → mod-helper 0 45 (46 * k) 45 ≡ 0
  div46k : ∀ k → div-helper 0 45 (46 * k) 45 ≡ k
  mod-a+598 : ∀ a → mod-helper 0 45 (a + 598) 45 ≡ mod-helper 0 45 a 45

{-# REWRITE mod46k #-}
{-# REWRITE div46k #-}
{-# REWRITE mod-a+598 #-}
