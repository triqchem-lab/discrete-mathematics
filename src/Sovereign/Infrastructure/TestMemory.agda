{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Infrastructure.TestMemory
-- 跨层 import 可达性核验件 —— 六层链路的编译期记忆测试。
--
-- 数学背景：本件不含定理，功能是**编译期可达性见证**：一次性 import 六层各代表件
--   （Base.Trit / Base.Invariants / Synthesis.T6 / Synthesis.A4Group /
--   Algebra.Jacobian.Matrix …），若任一层接口失效则本件立刻编译失败，
--   从而把「层间接口连通性」变成可自动核验的门禁信号。
module Sovereign.Infrastructure.TestMemory where
open import Sovereign.Base.Trit
open import Sovereign.Base.Invariants
open import Sovereign.Synthesis.Combinatorics.T6
open import Sovereign.Synthesis.A4.A4Group
open import Sovereign.Algebra.Jacobian.Matrix
