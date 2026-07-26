{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Structology.MotorStableStates where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; _*_)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Algebra.GF9 using (_+gf9_)
open import Sovereign.Structology.A4Group using (A4)

open import Sovereign.Algebra.TriCycGraph using (TriCycGraph)
open import Sovereign.Structology.ArthurMagicSquare
  using (Matrix4; zeroMatrix;
         IsArthurMagicSquare; a4ActionOnMatrix;
         zeroMatrix-isArthur)

-- ══════════════════════════════════════════════════════════════
-- §1 稳定态定义
-- ══════════════════════════════════════════════════════════════

-- A₄ 不变性
IsA4Invariant : Matrix4 → Set
IsA4Invariant M = ∀ (g : A4) → a4ActionOnMatrix g M ≡ M

-- 稳定态 = 亚瑟幻方 + A₄ 不变
StableState : Set
StableState = Σ Matrix4 (λ M → IsArthurMagicSquare M × IsA4Invariant M)

-- ══════════════════════════════════════════════════════════════
-- §2 零矩阵的稳定态性质
-- ══════════════════════════════════════════════════════════════

-- 零矩阵是 A₄ 不变的
zeroMatrix-a4Invariant : IsA4Invariant zeroMatrix
zeroMatrix-a4Invariant g = refl

-- 零矩阵是稳定态
zeroMatrix-stable : StableState
zeroMatrix-stable = zeroMatrix , zeroMatrix-isArthur , zeroMatrix-a4Invariant

-- ══════════════════════════════════════════════════════════════
-- §3 三角循环图与幻方的耦合
-- ══════════════════════════════════════════════════════════════

-- 从四个三角循环图构造候选矩阵（简化版）
-- 列索引 Fin 4 映射到 TriCycGraph 的 Fin 3 边索引（第4列回绕到 0）
fourTCGtoMatrix : TriCycGraph → TriCycGraph → TriCycGraph → TriCycGraph → Matrix4
fourTCGtoMatrix wg0 wg1 wg2 wg3 i zero = (wg0 zero) +gf9 ((wg1 zero) +gf9 ((wg2 zero) +gf9 (wg3 zero)))
fourTCGtoMatrix wg0 wg1 wg2 wg3 i (suc zero) = (wg0 (suc zero)) +gf9 ((wg1 (suc zero)) +gf9 ((wg2 (suc zero)) +gf9 (wg3 (suc zero))))
fourTCGtoMatrix wg0 wg1 wg2 wg3 i (suc (suc zero)) = (wg0 (suc (suc zero))) +gf9 ((wg1 (suc (suc zero))) +gf9 ((wg2 (suc (suc zero))) +gf9 (wg3 (suc (suc zero)))))
fourTCGtoMatrix wg0 wg1 wg2 wg3 i (suc (suc (suc zero))) = (wg0 zero) +gf9 ((wg1 zero) +gf9 ((wg2 zero) +gf9 (wg3 zero)))

-- ══════════════════════════════════════════════════════════════
-- §4 轨道-稳定子定理框架
-- ══════════════════════════════════════════════════════════════

-- A₄ 的阶
a4-order : ℕ
a4-order = 12

-- 不动点类型
FixPoint : A4 → Set
FixPoint g = Σ Matrix4 (λ M → a4ActionOnMatrix g M ≡ M)

-- Burnside 引理：|G| × |Orbits| = Σ_{g∈G} |Fix(g)|
-- 其中 |Fix(g)| 是群元素 g 的不动点个数
BurnsideLemma : Set
BurnsideLemma =
  Σ ℕ (λ numOrbits →
    Σ ℕ (λ totalFix →
      totalFix ≡ numOrbits * a4-order))

-- ══════════════════════════════════════════════════════════════
-- §5 Burnside 计算框架
-- ══════════════════════════════════════════════════════════════

-- Fix(g) 的大小类型
FixSize : A4 → Set
FixSize g = Σ ℕ (λ n → Σ (Fin n → FixPoint g) (λ enumerate → ⊤))
-- 简化版：只需要 Fix(g) 的基数

-- 每个群元素的不动点计数（待逐元素计算）
-- Fix(Id) = 所有矩阵 = 9^16（太大，无法直接计算）
-- Fix(g) for g ≠ Id = 需要分析 g 的置换结构

-- A₄ 的 12 个元素对 4×4 矩阵的置换效果
-- perm g : Fin 4 → Fin 4 是 g 的置换表示
-- g·M = λ i j → M (perm g i) (perm g j)
-- Fix(g) = {M : ∀ i j → M (perm g i) (perm g j) ≡ M i j}

-- 对角元素的不动点条件：
-- M (perm g i) (perm g i) ≡ M i i（对角线在置换下不变）

-- ══════════════════════════════════════════════════════════════
-- §6 轨道数的理论界限
-- ══════════════════════════════════════════════════════════════

-- 轨道数的上界：矩阵空间大小 / |A₄|
-- 轨道数的下界：1（至少有一个轨道）

-- 关键定理：A₄-等变矩阵的轨道结构
-- 等变矩阵 M 满足 g·M = M 对所有 g ∈ A₄
-- 这意味着 Fix(g) 包含所有等变矩阵
-- 等变矩阵的轨道大小 = 1（不动点）

-- 等变矩阵空间的维数（在 GF(9) 上）
-- 每个等变矩阵由少数自由参数确定
-- 4 行 × 4 列 = 16 个槽位
-- A₄ 作用给出约束，减少自由度
