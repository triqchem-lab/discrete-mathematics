{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.MatrixZω
-- Z[ω] 上的最小矩阵库 — A₄ 三维表示 ρ₃ 构造的基础设施 (0 postulate)
--
-- 矩阵用 Vec (Vec Zω m) n 表示 (n 行 m 列), 提供:
--   dot (向量内积), mulMat (矩阵乘法), trace (迹)。
-- 全部递归/定义展开, 无 postulate。

module Sovereign.Structology.MatrixZω where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero)
open import Data.Vec using (Vec; []; _∷_; map; lookup; allFin; tail)

open import Sovereign.Structology.A4Representation
  using (Zω; addZω; mulZω; zeroZω; oneZω; negZω)

--------------------------------------------------------------------------------
-- 矩阵与向量
--------------------------------------------------------------------------------

Mat : ℕ → ℕ → Set
Mat n m = Vec (Vec Zω m) n

-- 向量内积: Σᵢ xᵢ · yᵢ
dot : ∀ {m} → Vec Zω m → Vec Zω m → Zω
dot [] [] = zeroZω
dot (x ∷ xs) (y ∷ ys) = addZω (mulZω x y) (dot xs ys)

-- 向量和: Σᵢ xᵢ
sumVec : ∀ {m} → Vec Zω m → Zω
sumVec [] = zeroZω
sumVec (x ∷ xs) = addZω x (sumVec xs)

-- 列提取: 矩阵 M 的第 j 列 (作为 n 维向量)
column : ∀ {n m} → Mat n m → Fin m → Vec Zω n
column M j = map (λ row → lookup row j) M

-- 矩阵乘法: (n×m)·(m×k) = n×k
mulMat : ∀ {n m k} → Mat n m → Mat m k → Mat n k
mulMat {k = k} A B = map (λ row → map (λ j → dot row (column B j)) (allFin k)) A

-- 迹: 对角和 Σᵢ Mᵢᵢ (去掉首行首列递归)
trace : ∀ {n} → Mat n n → Zω
trace [] = zeroZω
trace (row ∷ rows) = addZω (lookup row zero) (trace (map tail rows))

-- 0 postulate.
