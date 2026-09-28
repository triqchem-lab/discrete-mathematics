{-# OPTIONS --rewriting --guardedness #-}

-- | PGM P2 验收探针 ②：把 12 层 mixedOp 嵌套**写开**作规则（LHS 头部仍是已定义符号）
-- 靶：变更 B（同 ①，但 LHS 不经 `mixedOp^12` 缩写，直接面对 `mixedOp` 定义）
-- 基线（未打补丁，实测）：rc=42，-W[no]RewriteLHSReduces
-- 期望（P2 生效后）：rc=0
-- 说明：`nested-law` 用 postulate 是**探针惯例**（本探针测的是内核接受/拒绝规则的判据，
--   不是数学命题本身；Pgm1 用的是库内已证定理，两条路径互为对照）。
module Pgm2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Equality.Rewrite
open import Sovereign.Base.Trit using (T₁)
open import Sovereign.Algebra.GroupTheory.DuodecClock using (DuodecPoint; mixedOp; a1)

postulate
  nested-law : ∀ (p : DuodecPoint) →
    mixedOp (T₁ , a1) (mixedOp (T₁ , a1) (mixedOp (T₁ , a1) (mixedOp (T₁ , a1)
    (mixedOp (T₁ , a1) (mixedOp (T₁ , a1) (mixedOp (T₁ , a1) (mixedOp (T₁ , a1)
    (mixedOp (T₁ , a1) (mixedOp (T₁ , a1) (mixedOp (T₁ , a1) (mixedOp (T₁ , a1) p)))))))))))
    ≡ p

{-# REWRITE nested-law #-}
