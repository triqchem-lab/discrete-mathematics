{-# OPTIONS --rewriting --guardedness #-}

-- 【术语边界】本模块「幻方」= 数学数字幻方（行列对角线和相等）。
-- 非卢先生「矢量方向/变量计数」幻方（阶数 = 同时在变的矢量方向个数）。
-- 辨析与知识库依据见 docs/cross-level/magic-square-terminology.md

module Sovereign.Structology.ArthurMagicSquare where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (T₀)
open import Sovereign.Algebra.GF9
  using (GF9; _+gf9_)

-- ══════════════════════════════════════════════════════════════
-- §1 4阶矩阵基础
-- ══════════════════════════════════════════════════════════════

-- 4阶 GF(9)-值矩阵
Matrix4 : Set
Matrix4 = Fin 4 → Fin 4 → GF9

-- 零矩阵
zeroMatrix : Matrix4
zeroMatrix _ _ = (T₀ , T₀)

-- ── 求和辅助 ──

sum4 : GF9 → GF9 → GF9 → GF9 → GF9
sum4 a b c d = a +gf9 (b +gf9 (c +gf9 d))

-- ── 行和、列和、对角线和 ──

rowSum : Matrix4 → Fin 4 → GF9
rowSum M i = sum4 (M i zero) (M i (suc zero))
                   (M i (suc (suc zero))) (M i (suc (suc (suc zero))))

colSum : Matrix4 → Fin 4 → GF9
colSum M j = sum4 (M zero j) (M (suc zero) j)
                   (M (suc (suc zero)) j) (M (suc (suc (suc zero))) j)

diagSum : Matrix4 → GF9
diagSum M = sum4 (M zero zero) (M (suc zero) (suc zero))
                  (M (suc (suc zero)) (suc (suc zero)))
                  (M (suc (suc (suc zero))) (suc (suc (suc zero))))

antiDiagSum : Matrix4 → GF9
antiDiagSum M = sum4 (M zero (suc (suc (suc zero))))
                      (M (suc zero) (suc (suc zero)))
                      (M (suc (suc zero)) (suc zero))
                      (M (suc (suc (suc zero))) zero)

-- ══════════════════════════════════════════════════════════════
-- §2 传统幻方约束
-- ══════════════════════════════════════════════════════════════

-- 行和常数性
IsRowConstant : Matrix4 → Set
IsRowConstant M = rowSum M zero ≡ rowSum M (suc zero)
                × rowSum M (suc zero) ≡ rowSum M (suc (suc zero))
                × rowSum M (suc (suc zero)) ≡ rowSum M (suc (suc (suc zero)))

-- 列和常数性
IsColConstant : Matrix4 → Set
IsColConstant M = colSum M zero ≡ colSum M (suc zero)
                × colSum M (suc zero) ≡ colSum M (suc (suc zero))
                × colSum M (suc (suc zero)) ≡ colSum M (suc (suc (suc zero)))

-- 对角线和与行和一致
DiagMatchesRow : Matrix4 → Set
DiagMatchesRow M = diagSum M ≡ rowSum M zero
                 × antiDiagSum M ≡ rowSum M zero

-- 传统幻方约束
IsClassicalMagicSquare : Matrix4 → Set
IsClassicalMagicSquare M = IsRowConstant M × IsColConstant M × DiagMatchesRow M

-- ══════════════════════════════════════════════════════════════
-- §3 A₄-等变约束（核心创新）
-- ══════════════════════════════════════════════════════════════
--
-- 亚瑟量子电机的幻方满足 A₄-等变约束。
-- A₄ 通过置换表示 perm : A4 → Fin 4 → Fin 4 作用于矩阵。

open import Sovereign.Structology.A4Group
  using (A4; Id; Rot; Flip; perm)

-- A₄ 在矩阵上的作用：重排行列索引
a4ActionOnMatrix : A4 → Matrix4 → Matrix4
a4ActionOnMatrix g M i j = M (perm g i) (perm g j)

-- A₄-等变行和约束
IsA4EquivariantRowSum : Matrix4 → Set
IsA4EquivariantRowSum M =
  ∀ (g : A4) (i : Fin 4) → rowSum (a4ActionOnMatrix g M) i ≡ rowSum M (perm g i)

-- V₄ 正规子群元素
v₄f₁ = Flip zero

v₄f₂ : A4
v₄f₂ = Flip (suc zero)

v₄f₃ : A4
v₄f₃ = Flip (suc (suc zero))

-- V₄ 作用下对角线和不变
IsV4DiagInvariant : Matrix4 → Set
IsV4DiagInvariant M =
  diagSum (a4ActionOnMatrix v₄f₁ M) ≡ diagSum M
  × diagSum (a4ActionOnMatrix v₄f₂ M) ≡ diagSum M
  × diagSum (a4ActionOnMatrix v₄f₃ M) ≡ diagSum M

-- ══════════════════════════════════════════════════════════════
-- §4 亚瑟幻方（完整约束）
-- ══════════════════════════════════════════════════════════════
--
-- 亚瑟幻方 = 传统幻方 + A₄-等变约束

IsArthurMagicSquare : Matrix4 → Set
IsArthurMagicSquare M =
  IsClassicalMagicSquare M × IsA4EquivariantRowSum M × IsV4DiagInvariant M

-- ══════════════════════════════════════════════════════════════
-- §5 解空间基础
-- ══════════════════════════════════════════════════════════════

-- 零矩阵是幻方
zeroMatrix-isRowConst : IsRowConstant zeroMatrix
zeroMatrix-isRowConst = refl , refl , refl

zeroMatrix-isColConst : IsColConstant zeroMatrix
zeroMatrix-isColConst = refl , refl , refl

zeroMatrix-diagMatches : DiagMatchesRow zeroMatrix
zeroMatrix-diagMatches = refl , refl

zeroMatrix-isClassical : IsClassicalMagicSquare zeroMatrix
zeroMatrix-isClassical = zeroMatrix-isRowConst , zeroMatrix-isColConst , zeroMatrix-diagMatches

-- 零矩阵的 A₄-等变性
zeroMatrix-a4Equiv : IsA4EquivariantRowSum zeroMatrix
zeroMatrix-a4Equiv g i = refl

-- 零矩阵的 V₄ 不变性
zeroMatrix-v4Diag : IsV4DiagInvariant zeroMatrix
zeroMatrix-v4Diag = refl , refl , refl

-- 零矩阵是亚瑟幻方
zeroMatrix-isArthur : IsArthurMagicSquare zeroMatrix
zeroMatrix-isArthur = zeroMatrix-isClassical , zeroMatrix-a4Equiv , zeroMatrix-v4Diag
