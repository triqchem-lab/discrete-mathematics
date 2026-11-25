{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.Matrix12Bounds
-- M14: 12×12 的三个登记数（1728 / 144 / 64）——不证明任何界（2026-11-26 勘误）
--
-- 本件是什么、不是什么（2026-11-26 勘误后的如实表述; 背景见
-- docs/techniques/M14-12x12矩阵指数上下界-2026-11-26.md 顶部勘误）:
--   · `gate-count-1728` 只证 12·12·12 ≡ 1728 这条算术恒等式。schoolbook（`*M12_`）每个输出
--     是 12 项点积、共 144 个输出, 所以「1728 次乘法」是对定义的读数; 库内没有形式化的
--     代价模型, 本件**不包含**「上界 1728」的定理。
--   · record `Matmul12Bounds` 只是登记三个数（1728 / 144 / 64）, 不证明任何界。
--     144 = 输出位置个数; 它**不是**已证的秩下界（见 Matrix12LowerWitness 头注）。
--   · 64 = TriRV 三进制 VM 跑 12×12 schoolbook 得到的「元素之和 mod 256」, 与宿主一致;
--     这是弱见证, 不是逐元素比对。
--
-- 未做: 12×12 矩阵乘法的双线性秩下界、形式代价模型、置换矩阵类的乘法次数。

module Sovereign.Algebra.LinearAlgebra.Matrix12Bounds where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- §1. 上界: schoolbook 乘法门数（可由 *M12_ 的定义结构定义性导出）
--------------------------------------------------------------------------------

-- 12·12 = 144 个输出, 每输出 12 项点积 → 12·12·12 = 1728 ⊗ 门
gate-count-1728 : 12 * 12 * 12 ≡ 1728
gate-count-1728 = refl

-- 144 = 输出位置个数（12·12）。这不是已证的秩下界（见头注）
independent-outputs : ℕ
independent-outputs = 144

--------------------------------------------------------------------------------
-- §2. 界限登记件（数值 oracle 冻结: 2026-11-26, trirv 实测 + 宿主交叉验证）
--------------------------------------------------------------------------------

record Matmul12Bounds : Set₁ where
  field
    -- 上界: schoolbook ⊗ 门数（*M12_ 定义性; TriRV 实测 71,264 步 ISA 级）
    upper-mult-gates : ℕ
    -- 144 = 输出位置个数。**不是**已证的秩下界（见头注）
    output-positions : ℕ
    -- TriRV 实测 checksum（宿主逐字一致）
    vm-checksum : ℕ

matmul12-bounds : Matmul12Bounds
matmul12-bounds = record
  { upper-mult-gates  = 12 * 12 * 12
  ; output-positions = 144
  ; vm-checksum = 64
  }
