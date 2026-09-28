{-# OPTIONS --guardedness #-}

-- | PGM P2 验收探针 ③：**只 import、不消费规则**，且自身不开 --rewriting
-- 靶：变更 A（规则集与定义集解耦 / 规则按作用域生效）
-- 基线（未打补丁，实测）：rc=42 [InfectiveImport]「using the --rewriting flag from a module which does not」
-- 期望（P2 生效后）：rc=0
module Infect where

open import Sovereign.Structology.T6 using (div3k)
