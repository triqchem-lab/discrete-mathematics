{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Base.FunctionTheory
-- 递归幂函数与零幂族 — 函数领域的第一性构造
--
-- 零幂族 (Zero Power Family):
--   零幂不是算术乘法 (0×0=0), 而是量子矢量相位回归的代数形式。
--   零是唯一能跨维度的元素: 0^n = 0 对所有 n ≥ 1。
--   零吸收一切幂次, 零的相位空间是单点 (无方向自由度)。
--   0² 不是"零的平方", 而是"零的二次幂 = 零" (零幂族)。
--   语料: "零的平方=零的五次方……零的一就等于零的N次方" (word_98)
--   语料: "只有0跨维度" / "0是一切的密码" (ppt_27, ppt_7)
--
-- 定位: 把幂函数从具体代数结构中抽象出来，作为递归函数论的基础。
-- 不依赖 GF(9) 或 Trit，避免循环依赖。
--
-- 核心定理:
--   §1 通用幂函数 power : (A→A→A) → A → ℕ → A
--   §2 幂等元幂稳定性: e*e=e → e^n=e
--   §3 零元幂吸收 (零幂族): 在含零元吸收律的结构中 0^(n+1)=0
--
-- 0 postulate.

module Sovereign.Base.FunctionTheory where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)

--------------------------------------------------------------------------------
-- §1. 通用幂函数
--------------------------------------------------------------------------------

-- 给定二元运算 op 和初始值 a，计算 a 的 n 次自作用
-- 约定: power op a 0 = a (不是单位元，因为通用结构无单位)
power : {A : Set} → (A → A → A) → A → ℕ → A
power op a zero    = a
power op a (suc n) = op a (power op a n)

-- 变体: power-one (以单位元为基底)
-- 需要具体结构提供 one，此处仅定义接口
power-with-one : {A : Set} → (A → A → A) → A → A → ℕ → A
power-with-one op one a zero    = one
power-with-one op one a (suc n) = op a (power-with-one op one a n)

--------------------------------------------------------------------------------
-- §2. 幂等元幂稳定性
--------------------------------------------------------------------------------

-- 若 e 是幂等元 (op e e ≡ e)，则 e 的任意正整数次幂等于 e
idempotent-power : {A : Set} (op : A → A → A) (e : A)
  → (op e e ≡ e)
  → ∀ n → power op e (suc n) ≡ e
idempotent-power op e idem zero    = idem
idempotent-power op e idem (suc n) =
  trans (cong (op e) (idempotent-power op e idem n)) idem

-- 幂等元的幂序列恒定: power op e n ≡ e (对所有 n ≥ 1)
-- 这是 "零的平方=零的六次方=零的N次方" 的抽象形式

--------------------------------------------------------------------------------
-- §3. 零元幂吸收 (通用版本)
--------------------------------------------------------------------------------

-- 在含零元吸收律 (zero-op : ∀ x → op zero x ≡ zero) 的结构中
-- zero 的任意正整数次幂为 zero
zero-power-generic : {A : Set} (op : A → A → A) (z : A)
  → (∀ x → op z x ≡ z)
  → ∀ n → power op z (suc n) ≡ z
zero-power-generic op z zero-op zero    = zero-op z
zero-power-generic op z zero-op (suc n) =
  trans (cong (op z) (zero-power-generic op z zero-op n)) (zero-op z)

-- 注意: 这个证明比 gf9-zero-mulˡ 更通用——它适用于任何满足零乘吸收的结构

-- 0 postulate.
