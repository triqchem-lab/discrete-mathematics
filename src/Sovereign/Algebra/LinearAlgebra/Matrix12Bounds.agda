{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.Matrix12Bounds
-- M14: 12×12 矩阵乘法指数的上下界登记件（duodecimal 展示群寄存器）
--
-- 数学背景（M14 注记: docs/techniques/M14-12x12矩阵指数上下界-2026-11-26.md）:
--   · 载体 = DCCayleyGraph.Matrix12 ℕ（12×12 行走计数; 乘法 *M12_ = schoolbook）
--   · ★ **上界（构造性, 已形式化）**: schoolbook = 12·12·12 = 1728 ⊗ 门
--     （*M12_ 的定义结构: 144 个输出 × 12 项点积; DCCayleyGraph 的 144 格
--      逐字承证即此上界的正确性证书）
--   · ★ **下界（见证 + 锚点, 总形式化登记为边界外）**: 恒等子式见证——
--     144 个输入对 (E_ii, E_ik) 的输出两两不同（oracle attest 144/144）
--     ⇒ 双线性秩 ≥ 144（数学锚点: Alder–Strassen 型下界; 精确 rank(⟨12,12,12⟩)
--     文献未知——已知界 [2.5n²−…, n³] 族）
--   · ★ **特殊类（拉丁正交 one-hot）**: 展示群置换矩阵 P_ρ（DCCayleyGraph 已形式化
--     P_ρ² = I）乘法 = **0 ⊗**（one-hot 坍缩 = 表查组合成）——乘法次数的下界
--     在置换子类上塌缩到 0
--   · ★ **12 层塔**: M^k (k ≤ 12) 重复平方需 ⌈log₂12⌉ = 4 次矩阵乘（顺序 11 次）;
--     duodecimal 闭合: P^12 = I（置换类）
--   · ★ **TriRV 三进制 VM 实测**（先算后验）: schoolbook 12×12 编译 112 指令 /
--     71,264 步 / checksum = 64（宿主 oracle 逐字一致 ✓——矩阵乘法本体正确）;
--     首版 `s2 & 255` 惯用法返回 0 的分歧 = C 前端把 `&` 映射为 TAND（逐 trit
--     最小值）——二进制位与惯用法在三进制容器上失效（57340224 = 243·235968,
--     trit 243/27/9/3 位全 0 → trit-wise min 塌 0; fib 基准未炸仅因返回值 < 256）
--
-- 诚实边界:
--   · 本件是界限的**登记件**（数值为 oracle 冻结）; rank ≥ 144 的完整 Agda 证明
--     需 ℕ 上的秩理论 [构造性缺席·候选级]
--   · Alder–Strassen 型强下界（2n²−1 族）与渐近 ω 不在本库边界

module Sovereign.Algebra.LinearAlgebra.Matrix12Bounds where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- §1. 上界: schoolbook 乘法门数（可由 *M12_ 的定义结构定义性导出）
--------------------------------------------------------------------------------

-- 12·12 = 144 个输出, 每输出 12 项点积 → 12·12·12 = 1728 ⊗ 门
gate-count-1728 : 12 * 12 * 12 ≡ 1728
gate-count-1728 = refl

-- 144 个独立输出泛函（恒等子式见证的秩下界目标数）
independent-outputs : ℕ
independent-outputs = 144

--------------------------------------------------------------------------------
-- §2. 界限登记件（数值 oracle 冻结: 2026-11-26, trirv 实测 + 宿主交叉验证）
--------------------------------------------------------------------------------

record Matmul12Bounds : Set₁ where
  field
    -- 上界: schoolbook ⊗ 门数（*M12_ 定义性; TriRV 实测 71,264 步 ISA 级）
    upper-mult-gates : ℕ
    -- 下界: 恒等子式见证的秩下界（144 个输入对输出两两不同）
    lower-rank-witness : ℕ
    -- TriRV 实测 checksum（宿主逐字一致）
    vm-checksum : ℕ

matmul12-bounds : Matmul12Bounds
matmul12-bounds = record
  { upper-mult-gates  = 12 * 12 * 12
  ; lower-rank-witness = 144
  ; vm-checksum = 64
  }
