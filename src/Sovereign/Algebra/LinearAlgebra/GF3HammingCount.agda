{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3HammingCount
-- 正确环上的 Hamming 计数（T4 修正版，2026-10-21）
--
-- 数学背景（2026-10-21 人类修正 —— 根本原因）
--   项目基底是**域塔**：GF(3) → GF(9)=GF(3)[x]/(x²+1) → …（不可约多项式 ⇒ **域** ✓，
--   有 Frobenius 自同构 σ(x)=x³ ✓，有 C₄ 相位 ✓，八要素齐 ✓）。
--   此前 T4 用的 `GF(3)[x]/(x³)` 是**幂零 thickening** ✗ —— 商环非域、Frobenius 打到零、
--   无相位、无刚性 ⇒ 八要素缺 ④⑦ ⇒ **不在展示群框架内** ⇒ 「数学基底不一样」= 无法闭合的根本原因。
--
--   正确环：`R_n = Functions((Z/3)^n, GF(3)) = GF(3)[x_j]/(x_j³ − x_j)`（**reduced** ✓）
--   在函数环里 `F = Σ x_j²` 是**点态乘法**（`x_j²` 是非零指示子）：
--        `(F · f)(x) = Hamming(x) mod 3 · f(x)`
--   ⇒ `F` 是**对角算子** ⇒ `a_n = dim ker F = #{x : Hamming(x) ≡ 0 mod 3}`。
--
-- 本模块
--   `C0/C1/C2`：Hamming 重量模 3 余 0/1/2 的点数（递归）
--   前四个值由内核 `refl` 核对
--   `C0#2` / `C0#3` / `C0#4`：`C_r(n+1) = 2·C_r(n) + C_{r−1}(n)` 的展开核对
--
-- ⚠ 未完成（诚实标注）：`total : C0 n + C1 n + C2 n ≡ 3^n` 与闭式
--   `C0(2m+1) = 9^m` 的 ℕ 归纳证明 —— 需要 ℕ 重排引理（本会话未做完）。
--   这两条已被 oracle `448d1d14`（n=1..10，域 88572）验证 ✓，但**不是** Agda 定理。
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3HammingCount where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

--------------------------------------------------------------------------------
-- §1. 三个计数（Hamming 重量模 3 的分布）
--------------------------------------------------------------------------------

C0 : ℕ → ℕ
C1 : ℕ → ℕ
C2 : ℕ → ℕ

C0 zero    = 1
C0 (suc n) = C0 n + 2 * C2 n

C1 zero    = 0
C1 (suc n) = C1 n + 2 * C0 n

C2 zero    = 0
C2 (suc n) = C2 n + 2 * C1 n

--------------------------------------------------------------------------------
-- §2. 前几个值（与 oracle `448d1d14` 对照：C0 = 1,1,1,9,33,81,225,729,2241,…）
--------------------------------------------------------------------------------

C0-zero : C0 0 ≡ 1
C0-zero = refl

C0-one : C0 1 ≡ 1
C0-one = refl

C0-two : C0 2 ≡ 1
C0-two = refl

C0-three : C0 3 ≡ 9
C0-three = refl

C0-four : C0 4 ≡ 33
C0-four = refl

C0-five : C0 5 ≡ 81
C0-five = refl

C0-six : C0 6 ≡ 225
C0-six = refl

C0-seven : C0 7 ≡ 729
C0-seven = refl

-- 奇数位闭式的四个实例（`C0 (2m+1) = 9^m`）
C0-odd-0 : C0 1 ≡ 9 ^ 0
C0-odd-0 = refl

C0-odd-1 : C0 3 ≡ 9 ^ 1
C0-odd-1 = refl

C0-odd-2 : C0 5 ≡ 9 ^ 2
C0-odd-2 = refl

C0-odd-3 : C0 7 ≡ 9 ^ 3
C0-odd-3 = refl

--------------------------------------------------------------------------------
-- §3. 递推的展开核对（`C_r(n+1) = 2·C_r(n) + C_{r−1}(n)`）
--------------------------------------------------------------------------------

C0-step : ∀ n → C0 (suc n) ≡ C0 n + 2 * C2 n
C0-step n = refl

C1-step : ∀ n → C1 (suc n) ≡ C1 n + 2 * C0 n
C1-step n = refl

C2-step : ∀ n → C2 (suc n) ≡ C2 n + 2 * C1 n
C2-step n = refl

--------------------------------------------------------------------------------
-- §4. 与 oracle 的对照（结构性事实，已被 oracle 验证；此处只做实例核对）
--------------------------------------------------------------------------------

-- oracle `448d1d14` 断言：a_n = C0 n，且在正确环上 c_n = a_n、q_n = 0。
-- 下列实例确保 `C0` 的定义与 oracle 的计数一致。
oracle-check : (C0 0 + C0 1 + C0 2 + C0 3 ≡ 1 + 1 + 1 + 9)
             × (C0 4 + C0 5 + C0 6 ≡ 33 + 81 + 225)
oracle-check = refl , refl
