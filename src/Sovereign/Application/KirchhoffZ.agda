{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.KirchhoffZ
-- Kirchhoff 矩阵与 Matrix-Tree 定理的 ℤ 实例核
--
-- 数学背景：Kirchhoff 1847 Matrix-Tree：K₃ 三角形 ℤ 系数——入射矩阵 M、Laplacian L=∂ᵀ∂、定理 A 行和零（电流定律离散形）、定理 B (n−1) 主子式 det=3=生成树数。
--   【域判断修正 2026-10-03】CRT 通道为正解（CRTDet 拱顶石），本模块 ℤ 版保留为精确值对照域（互补）。
--
-- 核心原则：
--   1. ℤ 精确值对照域（CRT 通道的互补面，非替代）
--   2. 定理 A/B 均为 K₃ 实例核
--   3. 域判断修正已入头（人类纠偏 2026-10-03）
--
-- 包含：M, sum3, L, rowsum-0, rowsum-1, rowsum-2, lap-rowsum-zero, det2ℤ, minor, matrix-tree-K3, L00, L01, L11, L12
--
module Sovereign.Application.KirchhoffZ where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Integer using (ℤ; 0ℤ; 1ℤ; +_; _+_; _*_; _-_; -_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- §1. K₃ 入射矩阵 M（边 × 顶点 → ℤ）
--
-- 边索引：0 = 边 01，1 = 边 12，2 = 边 20（定向：起点 −1、终点 +1）。
--------------------------------------------------------------------------------

M : Fin 3 → Fin 3 → ℤ
M fzero fzero = - 1ℤ                     -- 边 01 起点 0
M fzero (fsuc fzero) = 1ℤ                -- 边 01 终点 1
M fzero (fsuc (fsuc fzero)) = 0ℤ
M (fsuc fzero) fzero = 0ℤ
M (fsuc fzero) (fsuc fzero) = - 1ℤ       -- 边 12 起点 1
M (fsuc fzero) (fsuc (fsuc fzero)) = 1ℤ  -- 边 12 终点 2
M (fsuc (fsuc fzero)) fzero = 1ℤ         -- 边 20 终点 0
M (fsuc (fsuc fzero)) (fsuc fzero) = 0ℤ
M (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) = - 1ℤ  -- 边 20 起点 2

sum3 : (Fin 3 → ℤ) → ℤ
sum3 f = f fzero + (f (fsuc fzero) + f (fsuc (fsuc fzero)))

--------------------------------------------------------------------------------
-- §2. Kirchhoff Laplacian：L u v = Σ_e M e u · M e v（∂ᵀ∂，定义级）
--------------------------------------------------------------------------------

L : Fin 3 → Fin 3 → ℤ
L u v = sum3 (λ e → M e u * M e v)

--------------------------------------------------------------------------------
-- §3. 定理 A：行和零（Kirchhoff 电流定律的离散形）
--
-- 每行 (L u 0 + L u 1 + L u 2) ≡ 0ℤ——ℤ 字面量归约直接闭合。
--------------------------------------------------------------------------------

rowsum-0 : sum3 (L fzero) ≡ 0ℤ
rowsum-0 = refl

rowsum-1 : sum3 (L (fsuc fzero)) ≡ 0ℤ
rowsum-1 = refl

rowsum-2 : sum3 (L (fsuc (fsuc fzero))) ≡ 0ℤ
rowsum-2 = refl

lap-rowsum-zero : ∀ u → sum3 (L u) ≡ 0ℤ
lap-rowsum-zero fzero = rowsum-0
lap-rowsum-zero (fsuc fzero) = rowsum-1
lap-rowsum-zero (fsuc (fsuc fzero)) = rowsum-2

--------------------------------------------------------------------------------
-- §4. 定理 B：Matrix-Tree 实例——(n−1) 主子式 = 生成树数
--
-- 删第 0 行第 0 列的主子式：
--   [[ L 1 1, L 1 2 ], [ L 2 1, L 2 2 ]] = [[ 2, −1 ], [ −1, 2 ]]
--   det = 2·2 − (−1)·(−1) = 4 − 1 = 3 = K₃ 生成树数（3 棵：01+12, 01+20, 12+20）。
-- ℤ 域必要性：3 ≡ 0 (mod 3)，GF(3) 上此信息被模吞——与 Topology 的
-- χ ∈ ℤ 同口径。
--------------------------------------------------------------------------------

det2ℤ : ℤ → ℤ → ℤ → ℤ → ℤ
det2ℤ a b c d = (a * d) - (b * c)

minor : Fin 2 → Fin 2 → ℤ
minor fzero fzero = L (fsuc fzero) (fsuc fzero)
minor fzero (fsuc fzero) = L (fsuc fzero) (fsuc (fsuc fzero))
minor (fsuc fzero) fzero = L (fsuc (fsuc fzero)) (fsuc fzero)
minor (fsuc fzero) (fsuc fzero) = L (fsuc (fsuc fzero)) (fsuc (fsuc fzero))

-- Matrix-Tree 实例：主子式行列式 = 3 = K₃ 生成树数
matrix-tree-K3 : det2ℤ (minor fzero fzero) (minor fzero (fsuc fzero))
                       (minor (fsuc fzero) fzero) (minor (fsuc fzero) (fsuc fzero))
               ≡ (+ 3)
matrix-tree-K3 = refl

--------------------------------------------------------------------------------
-- §5. 具体点对抗（对抗验证协议 §6）：L 分量独立 refl
--
-- 对照 BoundaryGF3 的 ∂₁（GF(3) 版）：ℤ 侧分量值独立归约，
-- 域差异可见——GF(3) 的 L 11 = 2 ≡ −1，ℤ 的 L 1 1 = 2 不回绕。
--------------------------------------------------------------------------------

L00 : L fzero fzero ≡ 1ℤ + 1ℤ
L00 = refl

L01 : L fzero (fsuc fzero) ≡ - 1ℤ
L01 = refl

L11 : L (fsuc fzero) (fsuc fzero) ≡ 1ℤ + 1ℤ
L11 = refl

L12 : L (fsuc fzero) (fsuc (fsuc fzero)) ≡ - 1ℤ
L12 = refl
