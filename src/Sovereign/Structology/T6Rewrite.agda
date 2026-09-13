{-# OPTIONS --rewriting --cubical --guardedness #-}

-- | Sovereign.Structology.T6Rewrite
-- T6 模块的 REWRITE 规则分离
--
-- 本模块只包含 REWRITE 规则，从 T6.agda 中分离出来
-- 以减少 的传染性，降低 All.agda 编译内存使用
--
-- 规则列表:
--   1. div3k: (3*k)/3 = k
--   2. mod3k: (3*k)%3 = 0
--   3. gf3Toℕ-A4-inv: A4 群作用不改变 GF3 编码 (需要 T6 类型)
--
-- 注意: 本模块不导入 T6，避免循环依赖
-- gf3Toℕ-A4-inv 规则需要在导入 T6 的模块中重新定义

module Sovereign.Structology.T6Rewrite where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (div-helper; mod-helper; Nat; _*_)
open import Agda.Builtin.Equality.Rewrite

-- 4320D 基 3 归约规则: (3*k)/3 ≡ k, (3*k)%3 ≡ 0
postulate
  div3k : ∀ k → div-helper 0 2 (3 * k) 2 ≡ k
  mod3k : ∀ k → mod-helper 0 2 (3 * k) 2 ≡ 0

{-# REWRITE div3k #-}
{-# REWRITE mod3k #-}
