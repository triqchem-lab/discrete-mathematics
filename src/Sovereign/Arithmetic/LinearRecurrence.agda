{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Arithmetic.LinearRecurrence
-- 线性递推序列的 GF(3) 形——递推定义层 + Fib 型实例 + 特征方程骨架。
--
-- 数学背景：常系数线性递推 x(n+2) = a·x(n+1) + b·x(n) 的序列生成与特征方程
--   λ² = aλ + b 的求根骨架；GF(3) 特征形下系数运算是 Trit 的 ⊕/⊗。
--
-- 核心原则：
-- 1. 递推序列 = 结构递归生成器（runRec2——双初值驱动）
-- 2. 特征方程 = 求值骨架（charEval——λ² ⊕ neg(a⊗λ) ⊕ neg b 的 GF(3) 形）
-- 3. 常系数闭式（特征根法）立界注记（深件不硬拱）
-- 4. 复用零重证：Trit 环律直用（Base.Trit 信任基座）
--
-- 包含：runRec2/Fib3 · charEval · 核对层 · 立界注记

module Sovereign.Arithmetic.LinearRecurrence where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

-- §1 递推生成器（定义层）
-- runRec2 a b x0 x1 n = 由 x(n)=x0, x(n+1)=x1 与系数 a b 生成的第 n 项

runRec2 : Trit → Trit → Trit → Trit → ℕ → Trit
runRec2 a b x0 x1 zero        = x0
runRec2 a b x0 x1 (suc zero)  = x1
runRec2 a b x0 x1 (suc (suc n)) =
  (a ⊗ runRec2 a b x0 x1 (suc n)) ⊕ (b ⊗ runRec2 a b x0 x1 n)

-- Fib 型 GF(3) 形（a=b=T₁, x0=T₀, x1=T₁）
fib3 : ℕ → Trit
fib3 = runRec2 T₁ T₁ T₀ T₁

-- §2 特征方程骨架
-- charEval a b λ = λ² ⊖ a·λ ⊖ b 的 GF(3) 形（⊖ = ⊕ negate）
-- 特征根 ⟺ charEval ≡ T₀（求根面立界注记）

charEval : Trit → Trit → Trit → Trit
charEval a b λv = ((λv ⊗ λv) ⊕ (negate (a ⊗ λv))) ⊕ (negate b)

-- §3 核对层（具体值全 refl 级）
-- fib3 前五项：0,1,1,2,0（GF(3) 形——1+1=2=T₂）

check-rec2-0 : runRec2 T₁ T₁ T₀ T₁ 0 ≡ T₀
check-rec2-0 = refl

check-rec2-1 : runRec2 T₁ T₁ T₀ T₁ 1 ≡ T₁
check-rec2-1 = refl

check-fib3-2 : fib3 2 ≡ T₁
check-fib3-2 = refl

check-fib3-3 : fib3 3 ≡ T₂
check-fib3-3 = refl

check-fib3-4 : fib3 4 ≡ T₀
check-fib3-4 = refl

check-char-0 : charEval T₁ T₂ T₀ ≡ T₁
check-char-0 = refl

check-char-1 : charEval T₁ T₂ T₁ ≡ T₁
check-char-1 = refl

-- §4 立界注记（不设空壳签名）
-- (i) 一般递推步数归纳性质（runRec2 的求和/标量律——随需求批）
-- (ii) 常系数闭式（特征根法——GF(3) 重根情形需小心，深件）
-- (iii) 特征根判定定理（charEval root ⟹ 几何递推形）

