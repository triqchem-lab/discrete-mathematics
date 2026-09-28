{-# OPTIONS --rewriting --guardedness #-}

-- | PGM P2 验收探针 ①：以**已定义运算**上的定理作 REWRITE 规则
-- 靶：变更 B（允许展示规约的 LHS 可归约 / 或提供 stuck 包装）
-- 基线（未打补丁，实测）：rc=42，-W[no]RewriteLHSReduces
--   —— LHS 头部 `mixedOp` 由 `mixedOp^12` 展开而来，是**已定义**符号 ⇒ LHS 会归约 ⇒ 规则不合法
-- 期望（P2 生效后）：rc=0
module Pgm1 where

open import Agda.Builtin.Equality.Rewrite
open import Sovereign.Algebra.GroupTheory.DuodecClock using (mixedOp^12; mixedOp-12-cycle)

{-# REWRITE mixedOp-12-cycle #-}
