{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.KirchhoffZ
-- 任务书第四层·4.1：Kirchhoff 矩阵与 Matrix-Tree 定理（1847）的 ℤ 实例核
--
-- 数学背景：Kirchhoff, "Über die Auflösung der Gleichungen…"（Ann. Phys. 72
--   (1847), 497–508）：图的 Laplacian L = ∂ᵀ∂ 的任意 (n−1)×(n−1) 主子式 =
--   生成树数（Matrix-Tree 定理）。**域判断**：矩阵树定理在 GF(3) 上退化
--   （K₃ 树数 = 3 ≡ 0 被模吞掉），必须 ℤ——与 jac_Topology 的 χ = Σ(−1)ᵏ dim Hₖ
--   用 Data.Integer 同口径（本地 ℤ 先例）。
--
-- 本模块（K₃ 三角形实例，ℤ 系数）：
--   ① 入射矩阵 M : 边 × 顶点 → ℤ（M e v = ±1 按定向，第三顶点 0）；
--   ② Laplacian L u v = Σ_e M e u · M e v（∂ᵀ∂ 定义级）；
--   ③ 定理 A（行和零）：∀ u → Σ_v L u v ≡ 0ℤ —— Kirchhoff 电流定律的离散形；
--   ④ 定理 B（Matrix-Tree 实例）：K₃ 的 (n−1) 主子式 det = 3 = 生成树数。
--
-- 【域判断修正（2026-10-03，人类纠偏）】「必须 ℤ」是草率结论：本库正解是
--   CRT 通道——jac_CRTDet 拱顶石 det = crt12(det₃, det₄)，GF(3) 分量退化由
--   Fin 4 分量补全（3 mod 4 = 3 ≠ 0），重构即非零可判。见 KirchhoffCRT.agda。
--   本模块 ℤ 版保留为**精确值对照域**（CRT 通道给 mod 12 非零可判，ℤ 给
--   精确值 3），两者互补。
--
-- ⚠ 诚实边界：
--   1. 这是 Matrix-Tree 的**实例层**（K₃ 一个图的具象计算），一般 n 的
--      「任意主子式 = 树数」定理需要 ℤ 上行列式理论 + 生成树枚举，roadmap。
--   2. 证明全部由 ℤ 字面量归约闭合（refl）——9 个 M 分量 + 6 个 L 分量 +
--      3 个行和 + 1 个主子式，均在 refl 归约可达范围（≤27 case 纪律内）。
--   3. ∂₁ 形状与 BoundaryGF3 同构（域不同：GF(3) vs ℤ），接线注明不 import
--      （域参数化泛型是 roadmap）。
--   4. CRT 对照件：Problem/Hodge/KirchhoffCRT.agda（mod 12 非零可判通道）。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.KirchhoffZ where

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
-- ℤ 域必要性：3 ≡ 0 (mod 3)，GF(3) 上此信息被模吞——与 jac_Topology 的
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
