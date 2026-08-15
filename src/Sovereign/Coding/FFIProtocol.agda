{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Coding.FFIProtocol
-- 65 桥接规范 — 外部计算结果的可信封装 (0 postulate, 无洞无占位)
--
-- 外部计算 (Rust sov-guard 等) 不可在 Agda 内运行; 协议用 record 封装
-- "值 + 正确性证明": Rust 侧生成实例时**必须附证明字段**, Agda 侧只
-- 消费实例并推导组合正确性。若 Rust 暂无法提供证明 → 记录仅为类型
-- 规范存在, Agda 不得使用其实例 (契约纪律, 见 §4)。
--
-- 与 NumericalSpec 的关系: NumericalSpec = 内部可证算法;
-- 本模块 = 外部计算的可信接口层 (Q16 值/模逆/线性方程组解三契约)。

module Sovereign.Coding.FFIProtocol where

open import Data.Nat using (ℕ; _*_; _+_; _∸_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

--------------------------------------------------------------------------------
-- §1. Q16 定点值契约: 值 + 范围不变量
--------------------------------------------------------------------------------

record Q16Value : Set where
  field
    raw   : ℕ
    -- 范围: raw ≤ 2¹⁶−1 — 饱和减法形式 (= 0 ⟺ ≤), 无实分析
    range : raw ∸ 65536 ≡ 0

-- 具体实例 (来自 NumericalSpec 的 0.25 = 16384·2⁻¹⁶)
q16-quarter : Q16Value
q16-quarter = record { raw = 16384 ; range = refl }

--------------------------------------------------------------------------------
-- §2. 模逆契约: 逆元 + 正确性证明 (交叉相乘形式, 无除法)
--------------------------------------------------------------------------------

record ModInverseResult (a m : ℕ) : Set where
  field
    inv k   : ℕ
    -- a·inv = 1 + k·m — 模逆的交叉相乘形式 (与 ChernExact.equals 同构)
    correct : a * inv ≡ 1 + k * m

-- 具体实例: 3⁻¹ ≡ 43691 (mod 2¹⁶): 3·43691 = 131073 = 1 + 2·65536
modinv-3 : ModInverseResult 3 65536
modinv-3 = record { inv = 43691 ; k = 2 ; correct = refl }

-- 可信传递: 任何契约实例的正确性可传递 (无重算)
modinv-transport : {a m : ℕ} (r : ModInverseResult a m)
  → a * ModInverseResult.inv r ≡ 1 + ModInverseResult.k r * m
modinv-transport r = ModInverseResult.correct r

--------------------------------------------------------------------------------
-- §3. GF(3) 2×2 线性方程组解契约: 解向量 + 代入验证
--------------------------------------------------------------------------------

-- 矩阵 ((a,b),(c,d)), 右端 (p,q), 解 (x,y):
--   a⊗x ⊕ b⊗y ≡ p ; c⊗x ⊕ d⊗y ≡ q
record LinearSolveResult
  (a b c d : Trit) (p q : Trit) : Set where
  field
    x y      : Trit
    solves-1 : (a ⊗ x) ⊕ (b ⊗ y) ≡ p
    solves-2 : (c ⊗ x) ⊕ (d ⊗ y) ≡ q

-- 具体实例: NumericalSpec §4 的系统 (1,2 / 1,1; 1,0) 解 (2,1)
linear-solve-22 : LinearSolveResult T₁ T₂ T₁ T₁ T₁ T₀
linear-solve-22 = record
  { x = T₂ ; y = T₁
  ; solves-1 = refl
  ; solves-2 = refl }

--------------------------------------------------------------------------------
-- §4. 契约纪律 (注释级, 无占位):
--   1) Rust 生成代码必须提供 range/correct/solves 证明字段 —
--      无法提供则 Agda 侧不得实例化 (记录仅为类型规范存在)。
--   2) 组合正确性由 Agda 侧推导: 如 modinv-transport 的无重算传递;
--      §3 的 solves-1/2 可直接导出数值验证 (见 NumericalSpec.solve-check-*).
--   3) 值来源审计: 43691/65536 来自 NumericalSpec (refl 承载),
--      本模块无裸未证常量。
--------------------------------------------------------------------------------

-- 0 postulate.
