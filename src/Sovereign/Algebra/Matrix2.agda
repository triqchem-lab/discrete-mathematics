{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Matrix2
--
-- 2×2 矩阵的**参数化**定义（B 档「Mat2 合并」的基础设施）。
--
-- 数学背景：
--   库内原有 3 处独立的 2×2 矩阵定义，仅系数域不同：
--     · S3IsGL22.agda:37      Mat2   (Bool  = GF(2))
--     · SL23Cayley.agda:47    Mat2   (Fin 3 = GF(3))
--     · ProjectionDifferential.agda:244 Mat2x2 (Trit = GF(3))
--   乘法公式完全相同（4 项「积之和」），只是域运算名字不同。
--   本模块给出参数化版本：Mat2 F（F 为系数类型），乘法接受域的
--   加法与乘法作为参数。
--
-- 核心原则：
--   1. **参数化而非复制**：一次定义，三处复用
--   2. **零假设**：只要求 F : Set 和两个二元运算，不要求域公理
--   3. 0 postulate / 0 hole
--
-- 包含：Mat2 / mkMat2 / mulMat2 / addMat2 / zeroMat2 / idMat2 / trace

module Sovereign.Algebra.Matrix2 where

open import Data.Nat using (ℕ)

--------------------------------------------------------------------------------
-- §1. 参数化矩阵类型
--------------------------------------------------------------------------------

-- 2×2 矩阵（系数类型 F）
record Mat2 (F : Set) : Set where
  constructor mkMat2
  field
    m00 m01 m10 m11 : F

open Mat2 public

--------------------------------------------------------------------------------
-- §2. 参数化运算（接受域的加法与乘法）
--------------------------------------------------------------------------------

-- 矩阵乘法: (A · B)ᵢⱼ = Σₖ Aᵢₖ ⊗ Bₖⱼ
-- 参数 _+F_ 是域的加法, _*F_ 是域的乘法
mulMat2 : ∀ {F : Set} (_+F_ _*F_ : F → F → F) → Mat2 F → Mat2 F → Mat2 F
mulMat2 _+F_ _*F_ (mkMat2 a b c d) (mkMat2 e f g h) =
  mkMat2 (_+F_ (_*F_ a e) (_*F_ b g))
         (_+F_ (_*F_ a f) (_*F_ b h))
         (_+F_ (_*F_ c e) (_*F_ d g))
         (_+F_ (_*F_ c f) (_*F_ d h))

-- 矩阵加法
addMat2 : ∀ {F : Set} (_+F_ : F → F → F) → Mat2 F → Mat2 F → Mat2 F
addMat2 _+F_ (mkMat2 a b c d) (mkMat2 e f g h) =
  mkMat2 (_+F_ a e) (_+F_ b f) (_+F_ c g) (_+F_ d h)

-- 迹: tr(A) = a₀₀ + a₁₁
trace : ∀ {F : Set} (_+F_ : F → F → F) → Mat2 F → F
trace _+F_ (mkMat2 a _ _ d) = _+F_ a d

-- 行列式: det(A) = a₀₀·a₁₁ + a₀₁·a₁₀
det : ∀ {F : Set} (_+F_ _*F_ : F → F → F) → Mat2 F → F
det _+F_ _*F_ (mkMat2 a b c d) = _+F_ (_*F_ a d) (_*F_ b c)

--------------------------------------------------------------------------------
-- §3. 单位矩阵与零矩阵（需要域的单位元与零元）
--------------------------------------------------------------------------------

idMat2 : ∀ {F : Set} → F → F → Mat2 F
idMat2 1F 0F = mkMat2 1F 0F 0F 1F

zeroMat2 : ∀ {F : Set} → F → Mat2 F
zeroMat2 0F = mkMat2 0F 0F 0F 0F

{-
  §3 结论：
  ✓ Mat2 F / mkMat2 / m00 / m01 / m10 / m11 : 参数化矩阵类型
  ✓ mulMat2 / addMat2 / trace / det : 参数化运算（接受域运算）
  ✓ idMat2 / zeroMat2 : 单位/零矩阵

  ⚠ 待做（下一块）：把 S3IsGL22 / SL23Cayley / ProjectionDifferential
    三处的 Mat2 替换为 Mat2 F 的实例（需处理命名与导入冲突）。
-}
