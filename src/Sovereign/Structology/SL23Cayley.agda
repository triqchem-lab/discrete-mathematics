{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.SL23Cayley
-- SL(2,3) 的 Cayley 表与 576 对封闭性 (GF(3) 定义表示, 0 postulate)
--
-- 深度证明 (补充 BinaryTetrahedralDefiningRep): SL(2,3) = {det=1 的 GF(3) 2×2 矩阵},
-- 24 元素在矩阵乘法下封闭。本模块以 24×24 = 576 对 Cayley 表穷举证明同态:
--   toMat (x ⊗ y) ≡ mulMat2 (toMat x) (toMat y)
-- 封闭性亦由 det 乘法性保证 (det(AB)=det(A)det(B)=1), 此处显式穷举与理论一致。

module Sovereign.Structology.SL23Cayley where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open import Sovereign.Structology.BinaryTetrahedralDefiningRep using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23; orderOf)

-- B 档「Mat2 合并」: 复用 Sovereign.Algebra.Matrix2 的参数化矩阵定义。
open import Sovereign.Algebra.Matrix2 using () renaming (Mat2 to Mat2F; mkMat2 to mkMat2; mulMat2 to mulMat2F)
open import Sovereign.Algebra.Matrix2 as M2 using ()

--------------------------------------------------------------------------------
-- §1. GF(3) = Fin 3 算术
--------------------------------------------------------------------------------

add3 : Fin 3 → Fin 3 → Fin 3
add3 zero m = m
add3 (suc zero) zero = suc zero
add3 (suc zero) (suc zero) = suc (suc zero)
add3 (suc zero) (suc (suc zero)) = zero
add3 (suc (suc zero)) zero = suc (suc zero)
add3 (suc (suc zero)) (suc zero) = zero
add3 (suc (suc zero)) (suc (suc zero)) = suc zero

mul3 : Fin 3 → Fin 3 → Fin 3
mul3 zero _ = zero
mul3 (suc zero) m = m
mul3 (suc (suc zero)) zero = zero
mul3 (suc (suc zero)) (suc zero) = suc (suc zero)
mul3 (suc (suc zero)) (suc (suc zero)) = suc zero

--------------------------------------------------------------------------------
-- §2. 2×2 矩阵 over Fin 3
--------------------------------------------------------------------------------

-- Mat2 = 参数化矩阵的特例（系数域 GF(3) = Fin 3）
Mat2 : Set
Mat2 = Mat2F (Fin 3)

-- 字段投影 m00/m01/m10/m11 由 Matrix2 的 `open Mat2 public` 提供

-- 构造子 mat2 来自 Matrix2.mkMat2（导入时重命名）。在 SL23Cayley 内再定义为
-- 普通函数，使其可被下游模块 `using (mat2)` 导入（重命名构造子不随 using 导出）。
mat2 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Mat2
mat2 = mkMat2

mulMat2 : Mat2 → Mat2 → Mat2
mulMat2 = mulMat2F add3 mul3

--------------------------------------------------------------------------------
-- §3. SL(2,3) 的 24 个矩阵
--------------------------------------------------------------------------------

toMat : SL23 → Mat2
toMat g0 = mat2 zero (suc zero) (suc (suc zero)) zero
toMat g1 = mat2 zero (suc zero) (suc (suc zero)) (suc zero)
toMat g2 = mat2 zero (suc zero) (suc (suc zero)) (suc (suc zero))
toMat g3 = mat2 zero (suc (suc zero)) (suc zero) zero
toMat g4 = mat2 zero (suc (suc zero)) (suc zero) (suc zero)
toMat g5 = mat2 zero (suc (suc zero)) (suc zero) (suc (suc zero))
toMat g6 = mat2 (suc zero) zero zero (suc zero)
toMat g7 = mat2 (suc zero) zero (suc zero) (suc zero)
toMat g8 = mat2 (suc zero) zero (suc (suc zero)) (suc zero)
toMat g9 = mat2 (suc zero) (suc zero) zero (suc zero)
toMat g10 = mat2 (suc zero) (suc zero) (suc zero) (suc (suc zero))
toMat g11 = mat2 (suc zero) (suc zero) (suc (suc zero)) zero
toMat g12 = mat2 (suc zero) (suc (suc zero)) zero (suc zero)
toMat g13 = mat2 (suc zero) (suc (suc zero)) (suc zero) zero
toMat g14 = mat2 (suc zero) (suc (suc zero)) (suc (suc zero)) (suc (suc zero))
toMat g15 = mat2 (suc (suc zero)) zero zero (suc (suc zero))
toMat g16 = mat2 (suc (suc zero)) zero (suc zero) (suc (suc zero))
toMat g17 = mat2 (suc (suc zero)) zero (suc (suc zero)) (suc (suc zero))
toMat g18 = mat2 (suc (suc zero)) (suc zero) zero (suc (suc zero))
toMat g19 = mat2 (suc (suc zero)) (suc zero) (suc zero) (suc zero)
toMat g20 = mat2 (suc (suc zero)) (suc zero) (suc (suc zero)) zero
toMat g21 = mat2 (suc (suc zero)) (suc (suc zero)) zero (suc (suc zero))
toMat g22 = mat2 (suc (suc zero)) (suc (suc zero)) (suc zero) zero
toMat g23 = mat2 (suc (suc zero)) (suc (suc zero)) (suc (suc zero)) (suc zero)

--------------------------------------------------------------------------------
-- §4. Cayley 表 (24×24 = 576)
--------------------------------------------------------------------------------

_⊗_ : SL23 → SL23 → SL23
g0 ⊗ g0 = g15
g0 ⊗ g1 = g18
g0 ⊗ g2 = g21
g0 ⊗ g3 = g6
g0 ⊗ g4 = g9
g0 ⊗ g5 = g12
g0 ⊗ g6 = g0
g0 ⊗ g7 = g11
g0 ⊗ g8 = g20
g0 ⊗ g9 = g2
g0 ⊗ g10 = g14
g0 ⊗ g11 = g17
g0 ⊗ g12 = g1
g0 ⊗ g13 = g8
g0 ⊗ g14 = g23
g0 ⊗ g15 = g3
g0 ⊗ g16 = g13
g0 ⊗ g17 = g22
g0 ⊗ g18 = g5
g0 ⊗ g19 = g10
g0 ⊗ g20 = g16
g0 ⊗ g21 = g4
g0 ⊗ g22 = g7
g0 ⊗ g23 = g19
g1 ⊗ g0 = g17
g1 ⊗ g1 = g20
g1 ⊗ g2 = g23
g1 ⊗ g3 = g7
g1 ⊗ g4 = g10
g1 ⊗ g5 = g13
g1 ⊗ g6 = g1
g1 ⊗ g7 = g9
g1 ⊗ g8 = g19
g1 ⊗ g9 = g0
g1 ⊗ g10 = g12
g1 ⊗ g11 = g16
g1 ⊗ g12 = g2
g1 ⊗ g13 = g6
g1 ⊗ g14 = g22
g1 ⊗ g15 = g5
g1 ⊗ g16 = g14
g1 ⊗ g17 = g21
g1 ⊗ g18 = g4
g1 ⊗ g19 = g11
g1 ⊗ g20 = g15
g1 ⊗ g21 = g3
g1 ⊗ g22 = g8
g1 ⊗ g23 = g18
g2 ⊗ g0 = g16
g2 ⊗ g1 = g19
g2 ⊗ g2 = g22
g2 ⊗ g3 = g8
g2 ⊗ g4 = g11
g2 ⊗ g5 = g14
g2 ⊗ g6 = g2
g2 ⊗ g7 = g10
g2 ⊗ g8 = g18
g2 ⊗ g9 = g1
g2 ⊗ g10 = g13
g2 ⊗ g11 = g15
g2 ⊗ g12 = g0
g2 ⊗ g13 = g7
g2 ⊗ g14 = g21
g2 ⊗ g15 = g4
g2 ⊗ g16 = g12
g2 ⊗ g17 = g23
g2 ⊗ g18 = g3
g2 ⊗ g19 = g9
g2 ⊗ g20 = g17
g2 ⊗ g21 = g5
g2 ⊗ g22 = g6
g2 ⊗ g23 = g20
g3 ⊗ g0 = g6
g3 ⊗ g1 = g12
g3 ⊗ g2 = g9
g3 ⊗ g3 = g15
g3 ⊗ g4 = g21
g3 ⊗ g5 = g18
g3 ⊗ g6 = g3
g3 ⊗ g7 = g22
g3 ⊗ g8 = g13
g3 ⊗ g9 = g4
g3 ⊗ g10 = g19
g3 ⊗ g11 = g7
g3 ⊗ g12 = g5
g3 ⊗ g13 = g16
g3 ⊗ g14 = g10
g3 ⊗ g15 = g0
g3 ⊗ g16 = g20
g3 ⊗ g17 = g11
g3 ⊗ g18 = g1
g3 ⊗ g19 = g23
g3 ⊗ g20 = g8
g3 ⊗ g21 = g2
g3 ⊗ g22 = g17
g3 ⊗ g23 = g14
g4 ⊗ g0 = g8
g4 ⊗ g1 = g14
g4 ⊗ g2 = g11
g4 ⊗ g3 = g16
g4 ⊗ g4 = g22
g4 ⊗ g5 = g19
g4 ⊗ g6 = g4
g4 ⊗ g7 = g23
g4 ⊗ g8 = g12
g4 ⊗ g9 = g5
g4 ⊗ g10 = g20
g4 ⊗ g11 = g6
g4 ⊗ g12 = g3
g4 ⊗ g13 = g17
g4 ⊗ g14 = g9
g4 ⊗ g15 = g2
g4 ⊗ g16 = g18
g4 ⊗ g17 = g10
g4 ⊗ g18 = g0
g4 ⊗ g19 = g21
g4 ⊗ g20 = g7
g4 ⊗ g21 = g1
g4 ⊗ g22 = g15
g4 ⊗ g23 = g13
g5 ⊗ g0 = g7
g5 ⊗ g1 = g13
g5 ⊗ g2 = g10
g5 ⊗ g3 = g17
g5 ⊗ g4 = g23
g5 ⊗ g5 = g20
g5 ⊗ g6 = g5
g5 ⊗ g7 = g21
g5 ⊗ g8 = g14
g5 ⊗ g9 = g3
g5 ⊗ g10 = g18
g5 ⊗ g11 = g8
g5 ⊗ g12 = g4
g5 ⊗ g13 = g15
g5 ⊗ g14 = g11
g5 ⊗ g15 = g1
g5 ⊗ g16 = g19
g5 ⊗ g17 = g9
g5 ⊗ g18 = g2
g5 ⊗ g19 = g22
g5 ⊗ g20 = g6
g5 ⊗ g21 = g0
g5 ⊗ g22 = g16
g5 ⊗ g23 = g12
g6 ⊗ g0 = g0
g6 ⊗ g1 = g1
g6 ⊗ g2 = g2
g6 ⊗ g3 = g3
g6 ⊗ g4 = g4
g6 ⊗ g5 = g5
g6 ⊗ g6 = g6
g6 ⊗ g7 = g7
g6 ⊗ g8 = g8
g6 ⊗ g9 = g9
g6 ⊗ g10 = g10
g6 ⊗ g11 = g11
g6 ⊗ g12 = g12
g6 ⊗ g13 = g13
g6 ⊗ g14 = g14
g6 ⊗ g15 = g15
g6 ⊗ g16 = g16
g6 ⊗ g17 = g17
g6 ⊗ g18 = g18
g6 ⊗ g19 = g19
g6 ⊗ g20 = g20
g6 ⊗ g21 = g21
g6 ⊗ g22 = g22
g6 ⊗ g23 = g23
g7 ⊗ g0 = g1
g7 ⊗ g1 = g2
g7 ⊗ g2 = g0
g7 ⊗ g3 = g5
g7 ⊗ g4 = g3
g7 ⊗ g5 = g4
g7 ⊗ g6 = g7
g7 ⊗ g7 = g8
g7 ⊗ g8 = g6
g7 ⊗ g9 = g10
g7 ⊗ g10 = g11
g7 ⊗ g11 = g9
g7 ⊗ g12 = g13
g7 ⊗ g13 = g14
g7 ⊗ g14 = g12
g7 ⊗ g15 = g17
g7 ⊗ g16 = g15
g7 ⊗ g17 = g16
g7 ⊗ g18 = g20
g7 ⊗ g19 = g18
g7 ⊗ g20 = g19
g7 ⊗ g21 = g23
g7 ⊗ g22 = g21
g7 ⊗ g23 = g22
g8 ⊗ g0 = g2
g8 ⊗ g1 = g0
g8 ⊗ g2 = g1
g8 ⊗ g3 = g4
g8 ⊗ g4 = g5
g8 ⊗ g5 = g3
g8 ⊗ g6 = g8
g8 ⊗ g7 = g6
g8 ⊗ g8 = g7
g8 ⊗ g9 = g11
g8 ⊗ g10 = g9
g8 ⊗ g11 = g10
g8 ⊗ g12 = g14
g8 ⊗ g13 = g12
g8 ⊗ g14 = g13
g8 ⊗ g15 = g16
g8 ⊗ g16 = g17
g8 ⊗ g17 = g15
g8 ⊗ g18 = g19
g8 ⊗ g19 = g20
g8 ⊗ g20 = g18
g8 ⊗ g21 = g22
g8 ⊗ g22 = g23
g8 ⊗ g23 = g21
g9 ⊗ g0 = g20
g9 ⊗ g1 = g23
g9 ⊗ g2 = g17
g9 ⊗ g3 = g13
g9 ⊗ g4 = g7
g9 ⊗ g5 = g10
g9 ⊗ g6 = g9
g9 ⊗ g7 = g19
g9 ⊗ g8 = g1
g9 ⊗ g9 = g12
g9 ⊗ g10 = g16
g9 ⊗ g11 = g0
g9 ⊗ g12 = g6
g9 ⊗ g13 = g22
g9 ⊗ g14 = g2
g9 ⊗ g15 = g21
g9 ⊗ g16 = g5
g9 ⊗ g17 = g14
g9 ⊗ g18 = g15
g9 ⊗ g19 = g4
g9 ⊗ g20 = g11
g9 ⊗ g21 = g18
g9 ⊗ g22 = g3
g9 ⊗ g23 = g8
g10 ⊗ g0 = g19
g10 ⊗ g1 = g22
g10 ⊗ g2 = g16
g10 ⊗ g3 = g14
g10 ⊗ g4 = g8
g10 ⊗ g5 = g11
g10 ⊗ g6 = g10
g10 ⊗ g7 = g18
g10 ⊗ g8 = g2
g10 ⊗ g9 = g13
g10 ⊗ g10 = g15
g10 ⊗ g11 = g1
g10 ⊗ g12 = g7
g10 ⊗ g13 = g21
g10 ⊗ g14 = g0
g10 ⊗ g15 = g23
g10 ⊗ g16 = g4
g10 ⊗ g17 = g12
g10 ⊗ g18 = g17
g10 ⊗ g19 = g3
g10 ⊗ g20 = g9
g10 ⊗ g21 = g20
g10 ⊗ g22 = g5
g10 ⊗ g23 = g6
g11 ⊗ g0 = g18
g11 ⊗ g1 = g21
g11 ⊗ g2 = g15
g11 ⊗ g3 = g12
g11 ⊗ g4 = g6
g11 ⊗ g5 = g9
g11 ⊗ g6 = g11
g11 ⊗ g7 = g20
g11 ⊗ g8 = g0
g11 ⊗ g9 = g14
g11 ⊗ g10 = g17
g11 ⊗ g11 = g2
g11 ⊗ g12 = g8
g11 ⊗ g13 = g23
g11 ⊗ g14 = g1
g11 ⊗ g15 = g22
g11 ⊗ g16 = g3
g11 ⊗ g17 = g13
g11 ⊗ g18 = g16
g11 ⊗ g19 = g5
g11 ⊗ g20 = g10
g11 ⊗ g21 = g19
g11 ⊗ g22 = g4
g11 ⊗ g23 = g7
g12 ⊗ g0 = g11
g12 ⊗ g1 = g8
g12 ⊗ g2 = g14
g12 ⊗ g3 = g22
g12 ⊗ g4 = g19
g12 ⊗ g5 = g16
g12 ⊗ g6 = g12
g12 ⊗ g7 = g4
g12 ⊗ g8 = g23
g12 ⊗ g9 = g6
g12 ⊗ g10 = g5
g12 ⊗ g11 = g20
g12 ⊗ g12 = g9
g12 ⊗ g13 = g3
g12 ⊗ g14 = g17
g12 ⊗ g15 = g18
g12 ⊗ g16 = g10
g12 ⊗ g17 = g2
g12 ⊗ g18 = g21
g12 ⊗ g19 = g7
g12 ⊗ g20 = g0
g12 ⊗ g21 = g15
g12 ⊗ g22 = g13
g12 ⊗ g23 = g1
g13 ⊗ g0 = g9
g13 ⊗ g1 = g6
g13 ⊗ g2 = g12
g13 ⊗ g3 = g21
g13 ⊗ g4 = g18
g13 ⊗ g5 = g15
g13 ⊗ g6 = g13
g13 ⊗ g7 = g3
g13 ⊗ g8 = g22
g13 ⊗ g9 = g7
g13 ⊗ g10 = g4
g13 ⊗ g11 = g19
g13 ⊗ g12 = g10
g13 ⊗ g13 = g5
g13 ⊗ g14 = g16
g13 ⊗ g15 = g20
g13 ⊗ g16 = g11
g13 ⊗ g17 = g0
g13 ⊗ g18 = g23
g13 ⊗ g19 = g8
g13 ⊗ g20 = g1
g13 ⊗ g21 = g17
g13 ⊗ g22 = g14
g13 ⊗ g23 = g2
g14 ⊗ g0 = g10
g14 ⊗ g1 = g7
g14 ⊗ g2 = g13
g14 ⊗ g3 = g23
g14 ⊗ g4 = g20
g14 ⊗ g5 = g17
g14 ⊗ g6 = g14
g14 ⊗ g7 = g5
g14 ⊗ g8 = g21
g14 ⊗ g9 = g8
g14 ⊗ g10 = g3
g14 ⊗ g11 = g18
g14 ⊗ g12 = g11
g14 ⊗ g13 = g4
g14 ⊗ g14 = g15
g14 ⊗ g15 = g19
g14 ⊗ g16 = g9
g14 ⊗ g17 = g1
g14 ⊗ g18 = g22
g14 ⊗ g19 = g6
g14 ⊗ g20 = g2
g14 ⊗ g21 = g16
g14 ⊗ g22 = g12
g14 ⊗ g23 = g0
g15 ⊗ g0 = g3
g15 ⊗ g1 = g5
g15 ⊗ g2 = g4
g15 ⊗ g3 = g0
g15 ⊗ g4 = g2
g15 ⊗ g5 = g1
g15 ⊗ g6 = g15
g15 ⊗ g7 = g17
g15 ⊗ g8 = g16
g15 ⊗ g9 = g21
g15 ⊗ g10 = g23
g15 ⊗ g11 = g22
g15 ⊗ g12 = g18
g15 ⊗ g13 = g20
g15 ⊗ g14 = g19
g15 ⊗ g15 = g6
g15 ⊗ g16 = g8
g15 ⊗ g17 = g7
g15 ⊗ g18 = g12
g15 ⊗ g19 = g14
g15 ⊗ g20 = g13
g15 ⊗ g21 = g9
g15 ⊗ g22 = g11
g15 ⊗ g23 = g10
g16 ⊗ g0 = g4
g16 ⊗ g1 = g3
g16 ⊗ g2 = g5
g16 ⊗ g3 = g2
g16 ⊗ g4 = g1
g16 ⊗ g5 = g0
g16 ⊗ g6 = g16
g16 ⊗ g7 = g15
g16 ⊗ g8 = g17
g16 ⊗ g9 = g22
g16 ⊗ g10 = g21
g16 ⊗ g11 = g23
g16 ⊗ g12 = g19
g16 ⊗ g13 = g18
g16 ⊗ g14 = g20
g16 ⊗ g15 = g8
g16 ⊗ g16 = g7
g16 ⊗ g17 = g6
g16 ⊗ g18 = g14
g16 ⊗ g19 = g13
g16 ⊗ g20 = g12
g16 ⊗ g21 = g11
g16 ⊗ g22 = g10
g16 ⊗ g23 = g9
g17 ⊗ g0 = g5
g17 ⊗ g1 = g4
g17 ⊗ g2 = g3
g17 ⊗ g3 = g1
g17 ⊗ g4 = g0
g17 ⊗ g5 = g2
g17 ⊗ g6 = g17
g17 ⊗ g7 = g16
g17 ⊗ g8 = g15
g17 ⊗ g9 = g23
g17 ⊗ g10 = g22
g17 ⊗ g11 = g21
g17 ⊗ g12 = g20
g17 ⊗ g13 = g19
g17 ⊗ g14 = g18
g17 ⊗ g15 = g7
g17 ⊗ g16 = g6
g17 ⊗ g17 = g8
g17 ⊗ g18 = g13
g17 ⊗ g19 = g12
g17 ⊗ g20 = g14
g17 ⊗ g21 = g10
g17 ⊗ g22 = g9
g17 ⊗ g23 = g11
g18 ⊗ g0 = g22
g18 ⊗ g1 = g16
g18 ⊗ g2 = g19
g18 ⊗ g3 = g11
g18 ⊗ g4 = g14
g18 ⊗ g5 = g8
g18 ⊗ g6 = g18
g18 ⊗ g7 = g2
g18 ⊗ g8 = g10
g18 ⊗ g9 = g15
g18 ⊗ g10 = g1
g18 ⊗ g11 = g13
g18 ⊗ g12 = g21
g18 ⊗ g13 = g0
g18 ⊗ g14 = g7
g18 ⊗ g15 = g12
g18 ⊗ g16 = g23
g18 ⊗ g17 = g4
g18 ⊗ g18 = g9
g18 ⊗ g19 = g17
g18 ⊗ g20 = g3
g18 ⊗ g21 = g6
g18 ⊗ g22 = g20
g18 ⊗ g23 = g5
g19 ⊗ g0 = g23
g19 ⊗ g1 = g17
g19 ⊗ g2 = g20
g19 ⊗ g3 = g10
g19 ⊗ g4 = g13
g19 ⊗ g5 = g7
g19 ⊗ g6 = g19
g19 ⊗ g7 = g1
g19 ⊗ g8 = g9
g19 ⊗ g9 = g16
g19 ⊗ g10 = g0
g19 ⊗ g11 = g12
g19 ⊗ g12 = g22
g19 ⊗ g13 = g2
g19 ⊗ g14 = g6
g19 ⊗ g15 = g14
g19 ⊗ g16 = g21
g19 ⊗ g17 = g5
g19 ⊗ g18 = g11
g19 ⊗ g19 = g15
g19 ⊗ g20 = g4
g19 ⊗ g21 = g8
g19 ⊗ g22 = g18
g19 ⊗ g23 = g3
g20 ⊗ g0 = g21
g20 ⊗ g1 = g15
g20 ⊗ g2 = g18
g20 ⊗ g3 = g9
g20 ⊗ g4 = g12
g20 ⊗ g5 = g6
g20 ⊗ g6 = g20
g20 ⊗ g7 = g0
g20 ⊗ g8 = g11
g20 ⊗ g9 = g17
g20 ⊗ g10 = g2
g20 ⊗ g11 = g14
g20 ⊗ g12 = g23
g20 ⊗ g13 = g1
g20 ⊗ g14 = g8
g20 ⊗ g15 = g13
g20 ⊗ g16 = g22
g20 ⊗ g17 = g3
g20 ⊗ g18 = g10
g20 ⊗ g19 = g16
g20 ⊗ g20 = g5
g20 ⊗ g21 = g7
g20 ⊗ g22 = g19
g20 ⊗ g23 = g4
g21 ⊗ g0 = g13
g21 ⊗ g1 = g10
g21 ⊗ g2 = g7
g21 ⊗ g3 = g20
g21 ⊗ g4 = g17
g21 ⊗ g5 = g23
g21 ⊗ g6 = g21
g21 ⊗ g7 = g14
g21 ⊗ g8 = g5
g21 ⊗ g9 = g18
g21 ⊗ g10 = g8
g21 ⊗ g11 = g3
g21 ⊗ g12 = g15
g21 ⊗ g13 = g11
g21 ⊗ g14 = g4
g21 ⊗ g15 = g9
g21 ⊗ g16 = g1
g21 ⊗ g17 = g19
g21 ⊗ g18 = g6
g21 ⊗ g19 = g2
g21 ⊗ g20 = g22
g21 ⊗ g21 = g12
g21 ⊗ g22 = g0
g21 ⊗ g23 = g16
g22 ⊗ g0 = g12
g22 ⊗ g1 = g9
g22 ⊗ g2 = g6
g22 ⊗ g3 = g18
g22 ⊗ g4 = g15
g22 ⊗ g5 = g21
g22 ⊗ g6 = g22
g22 ⊗ g7 = g13
g22 ⊗ g8 = g3
g22 ⊗ g9 = g19
g22 ⊗ g10 = g7
g22 ⊗ g11 = g4
g22 ⊗ g12 = g16
g22 ⊗ g13 = g10
g22 ⊗ g14 = g5
g22 ⊗ g15 = g11
g22 ⊗ g16 = g0
g22 ⊗ g17 = g20
g22 ⊗ g18 = g8
g22 ⊗ g19 = g1
g22 ⊗ g20 = g23
g22 ⊗ g21 = g14
g22 ⊗ g22 = g2
g22 ⊗ g23 = g17
g23 ⊗ g0 = g14
g23 ⊗ g1 = g11
g23 ⊗ g2 = g8
g23 ⊗ g3 = g19
g23 ⊗ g4 = g16
g23 ⊗ g5 = g22
g23 ⊗ g6 = g23
g23 ⊗ g7 = g12
g23 ⊗ g8 = g4
g23 ⊗ g9 = g20
g23 ⊗ g10 = g6
g23 ⊗ g11 = g5
g23 ⊗ g12 = g17
g23 ⊗ g13 = g9
g23 ⊗ g14 = g3
g23 ⊗ g15 = g10
g23 ⊗ g16 = g2
g23 ⊗ g17 = g18
g23 ⊗ g18 = g7
g23 ⊗ g19 = g0
g23 ⊗ g20 = g21
g23 ⊗ g21 = g13
g23 ⊗ g22 = g1
g23 ⊗ g23 = g15

--------------------------------------------------------------------------------
-- §5. 同态: toMat (x ⊗ y) ≡ mulMat2 (toMat x) (toMat y)  (符号化: 24 行引理 × 24 案)
--
-- 【符号化说明】原实现是单引理 576 案 refl 表（全库最大单件，超「单引理 ≤27 案」纪律）。
-- 本节按第一参数分解为 24 个行引理 toMat-hom-g0..g23（每个 ∀ y，24 案 refl ≤27 ✓），
-- 再由 24 案调度器 toMat-hom 组装；签名不变，576 条核对事实逐条保留。
--
-- 【为何不能再压缩】SL23 是不透明 24 构造子 data（BinaryTetrahedralDefiningRep），
-- _⊗_ 是 576 条不透明查找表，无生成元/字表示可归纳——本定理的命题内容正是
-- 「表数据与矩阵乘法一致」的 576 条独立事实，逐条归约不可约。生成元路线须先证
-- 「表 = 字乘法」，那本身就是 576 案；重定义 _⊗_ 绕开表属循环论证，纪律禁止。
--------------------------------------------------------------------------------

-- 行引理 0: 固定左元 g0，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g0 : ∀ (y : SL23) → toMat (g0 ⊗ y) ≡ mulMat2 (toMat g0) (toMat y)
toMat-hom-g0 g0 = refl
toMat-hom-g0 g1 = refl
toMat-hom-g0 g2 = refl
toMat-hom-g0 g3 = refl
toMat-hom-g0 g4 = refl
toMat-hom-g0 g5 = refl
toMat-hom-g0 g6 = refl
toMat-hom-g0 g7 = refl
toMat-hom-g0 g8 = refl
toMat-hom-g0 g9 = refl
toMat-hom-g0 g10 = refl
toMat-hom-g0 g11 = refl
toMat-hom-g0 g12 = refl
toMat-hom-g0 g13 = refl
toMat-hom-g0 g14 = refl
toMat-hom-g0 g15 = refl
toMat-hom-g0 g16 = refl
toMat-hom-g0 g17 = refl
toMat-hom-g0 g18 = refl
toMat-hom-g0 g19 = refl
toMat-hom-g0 g20 = refl
toMat-hom-g0 g21 = refl
toMat-hom-g0 g22 = refl
toMat-hom-g0 g23 = refl

-- 行引理 1: 固定左元 g1，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g1 : ∀ (y : SL23) → toMat (g1 ⊗ y) ≡ mulMat2 (toMat g1) (toMat y)
toMat-hom-g1 g0 = refl
toMat-hom-g1 g1 = refl
toMat-hom-g1 g2 = refl
toMat-hom-g1 g3 = refl
toMat-hom-g1 g4 = refl
toMat-hom-g1 g5 = refl
toMat-hom-g1 g6 = refl
toMat-hom-g1 g7 = refl
toMat-hom-g1 g8 = refl
toMat-hom-g1 g9 = refl
toMat-hom-g1 g10 = refl
toMat-hom-g1 g11 = refl
toMat-hom-g1 g12 = refl
toMat-hom-g1 g13 = refl
toMat-hom-g1 g14 = refl
toMat-hom-g1 g15 = refl
toMat-hom-g1 g16 = refl
toMat-hom-g1 g17 = refl
toMat-hom-g1 g18 = refl
toMat-hom-g1 g19 = refl
toMat-hom-g1 g20 = refl
toMat-hom-g1 g21 = refl
toMat-hom-g1 g22 = refl
toMat-hom-g1 g23 = refl

-- 行引理 2: 固定左元 g2，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g2 : ∀ (y : SL23) → toMat (g2 ⊗ y) ≡ mulMat2 (toMat g2) (toMat y)
toMat-hom-g2 g0 = refl
toMat-hom-g2 g1 = refl
toMat-hom-g2 g2 = refl
toMat-hom-g2 g3 = refl
toMat-hom-g2 g4 = refl
toMat-hom-g2 g5 = refl
toMat-hom-g2 g6 = refl
toMat-hom-g2 g7 = refl
toMat-hom-g2 g8 = refl
toMat-hom-g2 g9 = refl
toMat-hom-g2 g10 = refl
toMat-hom-g2 g11 = refl
toMat-hom-g2 g12 = refl
toMat-hom-g2 g13 = refl
toMat-hom-g2 g14 = refl
toMat-hom-g2 g15 = refl
toMat-hom-g2 g16 = refl
toMat-hom-g2 g17 = refl
toMat-hom-g2 g18 = refl
toMat-hom-g2 g19 = refl
toMat-hom-g2 g20 = refl
toMat-hom-g2 g21 = refl
toMat-hom-g2 g22 = refl
toMat-hom-g2 g23 = refl

-- 行引理 3: 固定左元 g3，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g3 : ∀ (y : SL23) → toMat (g3 ⊗ y) ≡ mulMat2 (toMat g3) (toMat y)
toMat-hom-g3 g0 = refl
toMat-hom-g3 g1 = refl
toMat-hom-g3 g2 = refl
toMat-hom-g3 g3 = refl
toMat-hom-g3 g4 = refl
toMat-hom-g3 g5 = refl
toMat-hom-g3 g6 = refl
toMat-hom-g3 g7 = refl
toMat-hom-g3 g8 = refl
toMat-hom-g3 g9 = refl
toMat-hom-g3 g10 = refl
toMat-hom-g3 g11 = refl
toMat-hom-g3 g12 = refl
toMat-hom-g3 g13 = refl
toMat-hom-g3 g14 = refl
toMat-hom-g3 g15 = refl
toMat-hom-g3 g16 = refl
toMat-hom-g3 g17 = refl
toMat-hom-g3 g18 = refl
toMat-hom-g3 g19 = refl
toMat-hom-g3 g20 = refl
toMat-hom-g3 g21 = refl
toMat-hom-g3 g22 = refl
toMat-hom-g3 g23 = refl

-- 行引理 4: 固定左元 g4，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g4 : ∀ (y : SL23) → toMat (g4 ⊗ y) ≡ mulMat2 (toMat g4) (toMat y)
toMat-hom-g4 g0 = refl
toMat-hom-g4 g1 = refl
toMat-hom-g4 g2 = refl
toMat-hom-g4 g3 = refl
toMat-hom-g4 g4 = refl
toMat-hom-g4 g5 = refl
toMat-hom-g4 g6 = refl
toMat-hom-g4 g7 = refl
toMat-hom-g4 g8 = refl
toMat-hom-g4 g9 = refl
toMat-hom-g4 g10 = refl
toMat-hom-g4 g11 = refl
toMat-hom-g4 g12 = refl
toMat-hom-g4 g13 = refl
toMat-hom-g4 g14 = refl
toMat-hom-g4 g15 = refl
toMat-hom-g4 g16 = refl
toMat-hom-g4 g17 = refl
toMat-hom-g4 g18 = refl
toMat-hom-g4 g19 = refl
toMat-hom-g4 g20 = refl
toMat-hom-g4 g21 = refl
toMat-hom-g4 g22 = refl
toMat-hom-g4 g23 = refl

-- 行引理 5: 固定左元 g5，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g5 : ∀ (y : SL23) → toMat (g5 ⊗ y) ≡ mulMat2 (toMat g5) (toMat y)
toMat-hom-g5 g0 = refl
toMat-hom-g5 g1 = refl
toMat-hom-g5 g2 = refl
toMat-hom-g5 g3 = refl
toMat-hom-g5 g4 = refl
toMat-hom-g5 g5 = refl
toMat-hom-g5 g6 = refl
toMat-hom-g5 g7 = refl
toMat-hom-g5 g8 = refl
toMat-hom-g5 g9 = refl
toMat-hom-g5 g10 = refl
toMat-hom-g5 g11 = refl
toMat-hom-g5 g12 = refl
toMat-hom-g5 g13 = refl
toMat-hom-g5 g14 = refl
toMat-hom-g5 g15 = refl
toMat-hom-g5 g16 = refl
toMat-hom-g5 g17 = refl
toMat-hom-g5 g18 = refl
toMat-hom-g5 g19 = refl
toMat-hom-g5 g20 = refl
toMat-hom-g5 g21 = refl
toMat-hom-g5 g22 = refl
toMat-hom-g5 g23 = refl

-- 行引理 6: 固定左元 g6，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g6 : ∀ (y : SL23) → toMat (g6 ⊗ y) ≡ mulMat2 (toMat g6) (toMat y)
toMat-hom-g6 g0 = refl
toMat-hom-g6 g1 = refl
toMat-hom-g6 g2 = refl
toMat-hom-g6 g3 = refl
toMat-hom-g6 g4 = refl
toMat-hom-g6 g5 = refl
toMat-hom-g6 g6 = refl
toMat-hom-g6 g7 = refl
toMat-hom-g6 g8 = refl
toMat-hom-g6 g9 = refl
toMat-hom-g6 g10 = refl
toMat-hom-g6 g11 = refl
toMat-hom-g6 g12 = refl
toMat-hom-g6 g13 = refl
toMat-hom-g6 g14 = refl
toMat-hom-g6 g15 = refl
toMat-hom-g6 g16 = refl
toMat-hom-g6 g17 = refl
toMat-hom-g6 g18 = refl
toMat-hom-g6 g19 = refl
toMat-hom-g6 g20 = refl
toMat-hom-g6 g21 = refl
toMat-hom-g6 g22 = refl
toMat-hom-g6 g23 = refl

-- 行引理 7: 固定左元 g7，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g7 : ∀ (y : SL23) → toMat (g7 ⊗ y) ≡ mulMat2 (toMat g7) (toMat y)
toMat-hom-g7 g0 = refl
toMat-hom-g7 g1 = refl
toMat-hom-g7 g2 = refl
toMat-hom-g7 g3 = refl
toMat-hom-g7 g4 = refl
toMat-hom-g7 g5 = refl
toMat-hom-g7 g6 = refl
toMat-hom-g7 g7 = refl
toMat-hom-g7 g8 = refl
toMat-hom-g7 g9 = refl
toMat-hom-g7 g10 = refl
toMat-hom-g7 g11 = refl
toMat-hom-g7 g12 = refl
toMat-hom-g7 g13 = refl
toMat-hom-g7 g14 = refl
toMat-hom-g7 g15 = refl
toMat-hom-g7 g16 = refl
toMat-hom-g7 g17 = refl
toMat-hom-g7 g18 = refl
toMat-hom-g7 g19 = refl
toMat-hom-g7 g20 = refl
toMat-hom-g7 g21 = refl
toMat-hom-g7 g22 = refl
toMat-hom-g7 g23 = refl

-- 行引理 8: 固定左元 g8，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g8 : ∀ (y : SL23) → toMat (g8 ⊗ y) ≡ mulMat2 (toMat g8) (toMat y)
toMat-hom-g8 g0 = refl
toMat-hom-g8 g1 = refl
toMat-hom-g8 g2 = refl
toMat-hom-g8 g3 = refl
toMat-hom-g8 g4 = refl
toMat-hom-g8 g5 = refl
toMat-hom-g8 g6 = refl
toMat-hom-g8 g7 = refl
toMat-hom-g8 g8 = refl
toMat-hom-g8 g9 = refl
toMat-hom-g8 g10 = refl
toMat-hom-g8 g11 = refl
toMat-hom-g8 g12 = refl
toMat-hom-g8 g13 = refl
toMat-hom-g8 g14 = refl
toMat-hom-g8 g15 = refl
toMat-hom-g8 g16 = refl
toMat-hom-g8 g17 = refl
toMat-hom-g8 g18 = refl
toMat-hom-g8 g19 = refl
toMat-hom-g8 g20 = refl
toMat-hom-g8 g21 = refl
toMat-hom-g8 g22 = refl
toMat-hom-g8 g23 = refl

-- 行引理 9: 固定左元 g9，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g9 : ∀ (y : SL23) → toMat (g9 ⊗ y) ≡ mulMat2 (toMat g9) (toMat y)
toMat-hom-g9 g0 = refl
toMat-hom-g9 g1 = refl
toMat-hom-g9 g2 = refl
toMat-hom-g9 g3 = refl
toMat-hom-g9 g4 = refl
toMat-hom-g9 g5 = refl
toMat-hom-g9 g6 = refl
toMat-hom-g9 g7 = refl
toMat-hom-g9 g8 = refl
toMat-hom-g9 g9 = refl
toMat-hom-g9 g10 = refl
toMat-hom-g9 g11 = refl
toMat-hom-g9 g12 = refl
toMat-hom-g9 g13 = refl
toMat-hom-g9 g14 = refl
toMat-hom-g9 g15 = refl
toMat-hom-g9 g16 = refl
toMat-hom-g9 g17 = refl
toMat-hom-g9 g18 = refl
toMat-hom-g9 g19 = refl
toMat-hom-g9 g20 = refl
toMat-hom-g9 g21 = refl
toMat-hom-g9 g22 = refl
toMat-hom-g9 g23 = refl

-- 行引理 10: 固定左元 g10，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g10 : ∀ (y : SL23) → toMat (g10 ⊗ y) ≡ mulMat2 (toMat g10) (toMat y)
toMat-hom-g10 g0 = refl
toMat-hom-g10 g1 = refl
toMat-hom-g10 g2 = refl
toMat-hom-g10 g3 = refl
toMat-hom-g10 g4 = refl
toMat-hom-g10 g5 = refl
toMat-hom-g10 g6 = refl
toMat-hom-g10 g7 = refl
toMat-hom-g10 g8 = refl
toMat-hom-g10 g9 = refl
toMat-hom-g10 g10 = refl
toMat-hom-g10 g11 = refl
toMat-hom-g10 g12 = refl
toMat-hom-g10 g13 = refl
toMat-hom-g10 g14 = refl
toMat-hom-g10 g15 = refl
toMat-hom-g10 g16 = refl
toMat-hom-g10 g17 = refl
toMat-hom-g10 g18 = refl
toMat-hom-g10 g19 = refl
toMat-hom-g10 g20 = refl
toMat-hom-g10 g21 = refl
toMat-hom-g10 g22 = refl
toMat-hom-g10 g23 = refl

-- 行引理 11: 固定左元 g11，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g11 : ∀ (y : SL23) → toMat (g11 ⊗ y) ≡ mulMat2 (toMat g11) (toMat y)
toMat-hom-g11 g0 = refl
toMat-hom-g11 g1 = refl
toMat-hom-g11 g2 = refl
toMat-hom-g11 g3 = refl
toMat-hom-g11 g4 = refl
toMat-hom-g11 g5 = refl
toMat-hom-g11 g6 = refl
toMat-hom-g11 g7 = refl
toMat-hom-g11 g8 = refl
toMat-hom-g11 g9 = refl
toMat-hom-g11 g10 = refl
toMat-hom-g11 g11 = refl
toMat-hom-g11 g12 = refl
toMat-hom-g11 g13 = refl
toMat-hom-g11 g14 = refl
toMat-hom-g11 g15 = refl
toMat-hom-g11 g16 = refl
toMat-hom-g11 g17 = refl
toMat-hom-g11 g18 = refl
toMat-hom-g11 g19 = refl
toMat-hom-g11 g20 = refl
toMat-hom-g11 g21 = refl
toMat-hom-g11 g22 = refl
toMat-hom-g11 g23 = refl

-- 行引理 12: 固定左元 g12，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g12 : ∀ (y : SL23) → toMat (g12 ⊗ y) ≡ mulMat2 (toMat g12) (toMat y)
toMat-hom-g12 g0 = refl
toMat-hom-g12 g1 = refl
toMat-hom-g12 g2 = refl
toMat-hom-g12 g3 = refl
toMat-hom-g12 g4 = refl
toMat-hom-g12 g5 = refl
toMat-hom-g12 g6 = refl
toMat-hom-g12 g7 = refl
toMat-hom-g12 g8 = refl
toMat-hom-g12 g9 = refl
toMat-hom-g12 g10 = refl
toMat-hom-g12 g11 = refl
toMat-hom-g12 g12 = refl
toMat-hom-g12 g13 = refl
toMat-hom-g12 g14 = refl
toMat-hom-g12 g15 = refl
toMat-hom-g12 g16 = refl
toMat-hom-g12 g17 = refl
toMat-hom-g12 g18 = refl
toMat-hom-g12 g19 = refl
toMat-hom-g12 g20 = refl
toMat-hom-g12 g21 = refl
toMat-hom-g12 g22 = refl
toMat-hom-g12 g23 = refl

-- 行引理 13: 固定左元 g13，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g13 : ∀ (y : SL23) → toMat (g13 ⊗ y) ≡ mulMat2 (toMat g13) (toMat y)
toMat-hom-g13 g0 = refl
toMat-hom-g13 g1 = refl
toMat-hom-g13 g2 = refl
toMat-hom-g13 g3 = refl
toMat-hom-g13 g4 = refl
toMat-hom-g13 g5 = refl
toMat-hom-g13 g6 = refl
toMat-hom-g13 g7 = refl
toMat-hom-g13 g8 = refl
toMat-hom-g13 g9 = refl
toMat-hom-g13 g10 = refl
toMat-hom-g13 g11 = refl
toMat-hom-g13 g12 = refl
toMat-hom-g13 g13 = refl
toMat-hom-g13 g14 = refl
toMat-hom-g13 g15 = refl
toMat-hom-g13 g16 = refl
toMat-hom-g13 g17 = refl
toMat-hom-g13 g18 = refl
toMat-hom-g13 g19 = refl
toMat-hom-g13 g20 = refl
toMat-hom-g13 g21 = refl
toMat-hom-g13 g22 = refl
toMat-hom-g13 g23 = refl

-- 行引理 14: 固定左元 g14，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g14 : ∀ (y : SL23) → toMat (g14 ⊗ y) ≡ mulMat2 (toMat g14) (toMat y)
toMat-hom-g14 g0 = refl
toMat-hom-g14 g1 = refl
toMat-hom-g14 g2 = refl
toMat-hom-g14 g3 = refl
toMat-hom-g14 g4 = refl
toMat-hom-g14 g5 = refl
toMat-hom-g14 g6 = refl
toMat-hom-g14 g7 = refl
toMat-hom-g14 g8 = refl
toMat-hom-g14 g9 = refl
toMat-hom-g14 g10 = refl
toMat-hom-g14 g11 = refl
toMat-hom-g14 g12 = refl
toMat-hom-g14 g13 = refl
toMat-hom-g14 g14 = refl
toMat-hom-g14 g15 = refl
toMat-hom-g14 g16 = refl
toMat-hom-g14 g17 = refl
toMat-hom-g14 g18 = refl
toMat-hom-g14 g19 = refl
toMat-hom-g14 g20 = refl
toMat-hom-g14 g21 = refl
toMat-hom-g14 g22 = refl
toMat-hom-g14 g23 = refl

-- 行引理 15: 固定左元 g15，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g15 : ∀ (y : SL23) → toMat (g15 ⊗ y) ≡ mulMat2 (toMat g15) (toMat y)
toMat-hom-g15 g0 = refl
toMat-hom-g15 g1 = refl
toMat-hom-g15 g2 = refl
toMat-hom-g15 g3 = refl
toMat-hom-g15 g4 = refl
toMat-hom-g15 g5 = refl
toMat-hom-g15 g6 = refl
toMat-hom-g15 g7 = refl
toMat-hom-g15 g8 = refl
toMat-hom-g15 g9 = refl
toMat-hom-g15 g10 = refl
toMat-hom-g15 g11 = refl
toMat-hom-g15 g12 = refl
toMat-hom-g15 g13 = refl
toMat-hom-g15 g14 = refl
toMat-hom-g15 g15 = refl
toMat-hom-g15 g16 = refl
toMat-hom-g15 g17 = refl
toMat-hom-g15 g18 = refl
toMat-hom-g15 g19 = refl
toMat-hom-g15 g20 = refl
toMat-hom-g15 g21 = refl
toMat-hom-g15 g22 = refl
toMat-hom-g15 g23 = refl

-- 行引理 16: 固定左元 g16，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g16 : ∀ (y : SL23) → toMat (g16 ⊗ y) ≡ mulMat2 (toMat g16) (toMat y)
toMat-hom-g16 g0 = refl
toMat-hom-g16 g1 = refl
toMat-hom-g16 g2 = refl
toMat-hom-g16 g3 = refl
toMat-hom-g16 g4 = refl
toMat-hom-g16 g5 = refl
toMat-hom-g16 g6 = refl
toMat-hom-g16 g7 = refl
toMat-hom-g16 g8 = refl
toMat-hom-g16 g9 = refl
toMat-hom-g16 g10 = refl
toMat-hom-g16 g11 = refl
toMat-hom-g16 g12 = refl
toMat-hom-g16 g13 = refl
toMat-hom-g16 g14 = refl
toMat-hom-g16 g15 = refl
toMat-hom-g16 g16 = refl
toMat-hom-g16 g17 = refl
toMat-hom-g16 g18 = refl
toMat-hom-g16 g19 = refl
toMat-hom-g16 g20 = refl
toMat-hom-g16 g21 = refl
toMat-hom-g16 g22 = refl
toMat-hom-g16 g23 = refl

-- 行引理 17: 固定左元 g17，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g17 : ∀ (y : SL23) → toMat (g17 ⊗ y) ≡ mulMat2 (toMat g17) (toMat y)
toMat-hom-g17 g0 = refl
toMat-hom-g17 g1 = refl
toMat-hom-g17 g2 = refl
toMat-hom-g17 g3 = refl
toMat-hom-g17 g4 = refl
toMat-hom-g17 g5 = refl
toMat-hom-g17 g6 = refl
toMat-hom-g17 g7 = refl
toMat-hom-g17 g8 = refl
toMat-hom-g17 g9 = refl
toMat-hom-g17 g10 = refl
toMat-hom-g17 g11 = refl
toMat-hom-g17 g12 = refl
toMat-hom-g17 g13 = refl
toMat-hom-g17 g14 = refl
toMat-hom-g17 g15 = refl
toMat-hom-g17 g16 = refl
toMat-hom-g17 g17 = refl
toMat-hom-g17 g18 = refl
toMat-hom-g17 g19 = refl
toMat-hom-g17 g20 = refl
toMat-hom-g17 g21 = refl
toMat-hom-g17 g22 = refl
toMat-hom-g17 g23 = refl

-- 行引理 18: 固定左元 g18，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g18 : ∀ (y : SL23) → toMat (g18 ⊗ y) ≡ mulMat2 (toMat g18) (toMat y)
toMat-hom-g18 g0 = refl
toMat-hom-g18 g1 = refl
toMat-hom-g18 g2 = refl
toMat-hom-g18 g3 = refl
toMat-hom-g18 g4 = refl
toMat-hom-g18 g5 = refl
toMat-hom-g18 g6 = refl
toMat-hom-g18 g7 = refl
toMat-hom-g18 g8 = refl
toMat-hom-g18 g9 = refl
toMat-hom-g18 g10 = refl
toMat-hom-g18 g11 = refl
toMat-hom-g18 g12 = refl
toMat-hom-g18 g13 = refl
toMat-hom-g18 g14 = refl
toMat-hom-g18 g15 = refl
toMat-hom-g18 g16 = refl
toMat-hom-g18 g17 = refl
toMat-hom-g18 g18 = refl
toMat-hom-g18 g19 = refl
toMat-hom-g18 g20 = refl
toMat-hom-g18 g21 = refl
toMat-hom-g18 g22 = refl
toMat-hom-g18 g23 = refl

-- 行引理 19: 固定左元 g19，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g19 : ∀ (y : SL23) → toMat (g19 ⊗ y) ≡ mulMat2 (toMat g19) (toMat y)
toMat-hom-g19 g0 = refl
toMat-hom-g19 g1 = refl
toMat-hom-g19 g2 = refl
toMat-hom-g19 g3 = refl
toMat-hom-g19 g4 = refl
toMat-hom-g19 g5 = refl
toMat-hom-g19 g6 = refl
toMat-hom-g19 g7 = refl
toMat-hom-g19 g8 = refl
toMat-hom-g19 g9 = refl
toMat-hom-g19 g10 = refl
toMat-hom-g19 g11 = refl
toMat-hom-g19 g12 = refl
toMat-hom-g19 g13 = refl
toMat-hom-g19 g14 = refl
toMat-hom-g19 g15 = refl
toMat-hom-g19 g16 = refl
toMat-hom-g19 g17 = refl
toMat-hom-g19 g18 = refl
toMat-hom-g19 g19 = refl
toMat-hom-g19 g20 = refl
toMat-hom-g19 g21 = refl
toMat-hom-g19 g22 = refl
toMat-hom-g19 g23 = refl

-- 行引理 20: 固定左元 g20，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g20 : ∀ (y : SL23) → toMat (g20 ⊗ y) ≡ mulMat2 (toMat g20) (toMat y)
toMat-hom-g20 g0 = refl
toMat-hom-g20 g1 = refl
toMat-hom-g20 g2 = refl
toMat-hom-g20 g3 = refl
toMat-hom-g20 g4 = refl
toMat-hom-g20 g5 = refl
toMat-hom-g20 g6 = refl
toMat-hom-g20 g7 = refl
toMat-hom-g20 g8 = refl
toMat-hom-g20 g9 = refl
toMat-hom-g20 g10 = refl
toMat-hom-g20 g11 = refl
toMat-hom-g20 g12 = refl
toMat-hom-g20 g13 = refl
toMat-hom-g20 g14 = refl
toMat-hom-g20 g15 = refl
toMat-hom-g20 g16 = refl
toMat-hom-g20 g17 = refl
toMat-hom-g20 g18 = refl
toMat-hom-g20 g19 = refl
toMat-hom-g20 g20 = refl
toMat-hom-g20 g21 = refl
toMat-hom-g20 g22 = refl
toMat-hom-g20 g23 = refl

-- 行引理 21: 固定左元 g21，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g21 : ∀ (y : SL23) → toMat (g21 ⊗ y) ≡ mulMat2 (toMat g21) (toMat y)
toMat-hom-g21 g0 = refl
toMat-hom-g21 g1 = refl
toMat-hom-g21 g2 = refl
toMat-hom-g21 g3 = refl
toMat-hom-g21 g4 = refl
toMat-hom-g21 g5 = refl
toMat-hom-g21 g6 = refl
toMat-hom-g21 g7 = refl
toMat-hom-g21 g8 = refl
toMat-hom-g21 g9 = refl
toMat-hom-g21 g10 = refl
toMat-hom-g21 g11 = refl
toMat-hom-g21 g12 = refl
toMat-hom-g21 g13 = refl
toMat-hom-g21 g14 = refl
toMat-hom-g21 g15 = refl
toMat-hom-g21 g16 = refl
toMat-hom-g21 g17 = refl
toMat-hom-g21 g18 = refl
toMat-hom-g21 g19 = refl
toMat-hom-g21 g20 = refl
toMat-hom-g21 g21 = refl
toMat-hom-g21 g22 = refl
toMat-hom-g21 g23 = refl

-- 行引理 22: 固定左元 g22，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g22 : ∀ (y : SL23) → toMat (g22 ⊗ y) ≡ mulMat2 (toMat g22) (toMat y)
toMat-hom-g22 g0 = refl
toMat-hom-g22 g1 = refl
toMat-hom-g22 g2 = refl
toMat-hom-g22 g3 = refl
toMat-hom-g22 g4 = refl
toMat-hom-g22 g5 = refl
toMat-hom-g22 g6 = refl
toMat-hom-g22 g7 = refl
toMat-hom-g22 g8 = refl
toMat-hom-g22 g9 = refl
toMat-hom-g22 g10 = refl
toMat-hom-g22 g11 = refl
toMat-hom-g22 g12 = refl
toMat-hom-g22 g13 = refl
toMat-hom-g22 g14 = refl
toMat-hom-g22 g15 = refl
toMat-hom-g22 g16 = refl
toMat-hom-g22 g17 = refl
toMat-hom-g22 g18 = refl
toMat-hom-g22 g19 = refl
toMat-hom-g22 g20 = refl
toMat-hom-g22 g21 = refl
toMat-hom-g22 g22 = refl
toMat-hom-g22 g23 = refl

-- 行引理 23: 固定左元 g23，对 24 个右元逐案核对（24 案 refl ≤27 ✓）
toMat-hom-g23 : ∀ (y : SL23) → toMat (g23 ⊗ y) ≡ mulMat2 (toMat g23) (toMat y)
toMat-hom-g23 g0 = refl
toMat-hom-g23 g1 = refl
toMat-hom-g23 g2 = refl
toMat-hom-g23 g3 = refl
toMat-hom-g23 g4 = refl
toMat-hom-g23 g5 = refl
toMat-hom-g23 g6 = refl
toMat-hom-g23 g7 = refl
toMat-hom-g23 g8 = refl
toMat-hom-g23 g9 = refl
toMat-hom-g23 g10 = refl
toMat-hom-g23 g11 = refl
toMat-hom-g23 g12 = refl
toMat-hom-g23 g13 = refl
toMat-hom-g23 g14 = refl
toMat-hom-g23 g15 = refl
toMat-hom-g23 g16 = refl
toMat-hom-g23 g17 = refl
toMat-hom-g23 g18 = refl
toMat-hom-g23 g19 = refl
toMat-hom-g23 g20 = refl
toMat-hom-g23 g21 = refl
toMat-hom-g23 g22 = refl
toMat-hom-g23 g23 = refl

--------------------------------------------------------------------------------
-- §5b. 调度器: 按第一参数分派到行引理（24 案，无 refl 穷举）
--------------------------------------------------------------------------------

toMat-hom : ∀ (x y : SL23) → toMat (x ⊗ y) ≡ mulMat2 (toMat x) (toMat y)
toMat-hom g0 y = toMat-hom-g0 y
toMat-hom g1 y = toMat-hom-g1 y
toMat-hom g2 y = toMat-hom-g2 y
toMat-hom g3 y = toMat-hom-g3 y
toMat-hom g4 y = toMat-hom-g4 y
toMat-hom g5 y = toMat-hom-g5 y
toMat-hom g6 y = toMat-hom-g6 y
toMat-hom g7 y = toMat-hom-g7 y
toMat-hom g8 y = toMat-hom-g8 y
toMat-hom g9 y = toMat-hom-g9 y
toMat-hom g10 y = toMat-hom-g10 y
toMat-hom g11 y = toMat-hom-g11 y
toMat-hom g12 y = toMat-hom-g12 y
toMat-hom g13 y = toMat-hom-g13 y
toMat-hom g14 y = toMat-hom-g14 y
toMat-hom g15 y = toMat-hom-g15 y
toMat-hom g16 y = toMat-hom-g16 y
toMat-hom g17 y = toMat-hom-g17 y
toMat-hom g18 y = toMat-hom-g18 y
toMat-hom g19 y = toMat-hom-g19 y
toMat-hom g20 y = toMat-hom-g20 y
toMat-hom g21 y = toMat-hom-g21 y
toMat-hom g22 y = toMat-hom-g22 y
toMat-hom g23 y = toMat-hom-g23 y

--------------------------------------------------------------------------------
-- §6. 元素阶自证: g^(orderOf g) = I (24 refl, 替代外部 Python 枚举)
-- 宪法对齐: 标准库信任度=0, 阶数事实必须在库内自证
--------------------------------------------------------------------------------

matI : Mat2
matI = mat2 (suc zero) zero zero (suc zero)

powMat : Mat2 → ℕ → Mat2
powMat m Data.Nat.zero = matI
powMat m (Data.Nat.suc n) = mulMat2 m (powMat m n)

order-pow : ∀ (g : SL23) → powMat (toMat g) (orderOf g) ≡ matI
order-pow g0 = refl
order-pow g1 = refl
order-pow g2 = refl
order-pow g3 = refl
order-pow g4 = refl
order-pow g5 = refl
order-pow g6 = refl
order-pow g7 = refl
order-pow g8 = refl
order-pow g9 = refl
order-pow g10 = refl
order-pow g11 = refl
order-pow g12 = refl
order-pow g13 = refl
order-pow g14 = refl
order-pow g15 = refl
order-pow g16 = refl
order-pow g17 = refl
order-pow g18 = refl
order-pow g19 = refl
order-pow g20 = refl
order-pow g21 = refl
order-pow g22 = refl
order-pow g23 = refl

--------------------------------------------------------------------------------
-- §7. 阶的最小性: g^k ≢ I 负证 (1 ≤ k < orderOf g, 共 75 项)
-- order-pow (§6) + order-minimal (§7) 合证「orderOf 确为最小阶」
--------------------------------------------------------------------------------

-- Fin 3 可判等
eq3 : Fin 3 → Fin 3 → Bool
eq3 zero zero = true
eq3 zero (suc zero) = false
eq3 zero (suc (suc zero)) = false
eq3 (suc zero) zero = false
eq3 (suc zero) (suc zero) = true
eq3 (suc zero) (suc (suc zero)) = false
eq3 (suc (suc zero)) zero = false
eq3 (suc (suc zero)) (suc zero) = false
eq3 (suc (suc zero)) (suc (suc zero)) = true

-- 单位元判定
isI : Mat2 → Bool
isI A = eq3 (M2.m00 A) (suc zero) ∧ (eq3 (M2.m01 A) zero ∧ (eq3 (M2.m10 A) zero ∧ eq3 (M2.m11 A) (suc zero)))

isI-matI : isI matI ≡ true
isI-matI = refl

true≢false : true ≡ false → ⊥
true≢false ()

not-isI : ∀ {m} → isI m ≡ false → m ≢ matI
not-isI h eq = true≢false (trans (cong isI (sym eq)) h)

-- 每个元素的最小性检查规格 (阶 n 检查 k = 1..n-1; 阶 1 无负证)
min-checks : SL23 → Set
min-checks g0 = isI (powMat (toMat g0) 1) ≡ false × isI (powMat (toMat g0) 2) ≡ false × isI (powMat (toMat g0) 3) ≡ false
min-checks g1 = isI (powMat (toMat g1) 1) ≡ false × isI (powMat (toMat g1) 2) ≡ false × isI (powMat (toMat g1) 3) ≡ false × isI (powMat (toMat g1) 4) ≡ false × isI (powMat (toMat g1) 5) ≡ false
min-checks g2 = isI (powMat (toMat g2) 1) ≡ false × isI (powMat (toMat g2) 2) ≡ false
min-checks g3 = isI (powMat (toMat g3) 1) ≡ false × isI (powMat (toMat g3) 2) ≡ false × isI (powMat (toMat g3) 3) ≡ false
min-checks g4 = isI (powMat (toMat g4) 1) ≡ false × isI (powMat (toMat g4) 2) ≡ false × isI (powMat (toMat g4) 3) ≡ false × isI (powMat (toMat g4) 4) ≡ false × isI (powMat (toMat g4) 5) ≡ false
min-checks g5 = isI (powMat (toMat g5) 1) ≡ false × isI (powMat (toMat g5) 2) ≡ false
min-checks g6 = ⊤
min-checks g7 = isI (powMat (toMat g7) 1) ≡ false × isI (powMat (toMat g7) 2) ≡ false
min-checks g8 = isI (powMat (toMat g8) 1) ≡ false × isI (powMat (toMat g8) 2) ≡ false
min-checks g9 = isI (powMat (toMat g9) 1) ≡ false × isI (powMat (toMat g9) 2) ≡ false
min-checks g10 = isI (powMat (toMat g10) 1) ≡ false × isI (powMat (toMat g10) 2) ≡ false × isI (powMat (toMat g10) 3) ≡ false
min-checks g11 = isI (powMat (toMat g11) 1) ≡ false × isI (powMat (toMat g11) 2) ≡ false × isI (powMat (toMat g11) 3) ≡ false × isI (powMat (toMat g11) 4) ≡ false × isI (powMat (toMat g11) 5) ≡ false
min-checks g12 = isI (powMat (toMat g12) 1) ≡ false × isI (powMat (toMat g12) 2) ≡ false
min-checks g13 = isI (powMat (toMat g13) 1) ≡ false × isI (powMat (toMat g13) 2) ≡ false × isI (powMat (toMat g13) 3) ≡ false × isI (powMat (toMat g13) 4) ≡ false × isI (powMat (toMat g13) 5) ≡ false
min-checks g14 = isI (powMat (toMat g14) 1) ≡ false × isI (powMat (toMat g14) 2) ≡ false × isI (powMat (toMat g14) 3) ≡ false
min-checks g15 = isI (powMat (toMat g15) 1) ≡ false
min-checks g16 = isI (powMat (toMat g16) 1) ≡ false × isI (powMat (toMat g16) 2) ≡ false × isI (powMat (toMat g16) 3) ≡ false × isI (powMat (toMat g16) 4) ≡ false × isI (powMat (toMat g16) 5) ≡ false
min-checks g17 = isI (powMat (toMat g17) 1) ≡ false × isI (powMat (toMat g17) 2) ≡ false × isI (powMat (toMat g17) 3) ≡ false × isI (powMat (toMat g17) 4) ≡ false × isI (powMat (toMat g17) 5) ≡ false
min-checks g18 = isI (powMat (toMat g18) 1) ≡ false × isI (powMat (toMat g18) 2) ≡ false × isI (powMat (toMat g18) 3) ≡ false × isI (powMat (toMat g18) 4) ≡ false × isI (powMat (toMat g18) 5) ≡ false
min-checks g19 = isI (powMat (toMat g19) 1) ≡ false × isI (powMat (toMat g19) 2) ≡ false × isI (powMat (toMat g19) 3) ≡ false
min-checks g20 = isI (powMat (toMat g20) 1) ≡ false × isI (powMat (toMat g20) 2) ≡ false
min-checks g21 = isI (powMat (toMat g21) 1) ≡ false × isI (powMat (toMat g21) 2) ≡ false × isI (powMat (toMat g21) 3) ≡ false × isI (powMat (toMat g21) 4) ≡ false × isI (powMat (toMat g21) 5) ≡ false
min-checks g22 = isI (powMat (toMat g22) 1) ≡ false × isI (powMat (toMat g22) 2) ≡ false
min-checks g23 = isI (powMat (toMat g23) 1) ≡ false × isI (powMat (toMat g23) 2) ≡ false × isI (powMat (toMat g23) 3) ≡ false

-- 最小阶定理: ∀ g, 1 ≤ k < orderOf g ⟹ g^k ≢ I (75 项 refl 穷举)
order-minimal : ∀ (g : SL23) → min-checks g
order-minimal g0 = refl , refl , refl
order-minimal g1 = refl , refl , refl , refl , refl
order-minimal g2 = refl , refl
order-minimal g3 = refl , refl , refl
order-minimal g4 = refl , refl , refl , refl , refl
order-minimal g5 = refl , refl
order-minimal g6 = tt
order-minimal g7 = refl , refl
order-minimal g8 = refl , refl
order-minimal g9 = refl , refl
order-minimal g10 = refl , refl , refl
order-minimal g11 = refl , refl , refl , refl , refl
order-minimal g12 = refl , refl
order-minimal g13 = refl , refl , refl , refl , refl
order-minimal g14 = refl , refl , refl
order-minimal g15 = refl
order-minimal g16 = refl , refl , refl , refl , refl
order-minimal g17 = refl , refl , refl , refl , refl
order-minimal g18 = refl , refl , refl , refl , refl
order-minimal g19 = refl , refl , refl
order-minimal g20 = refl , refl
order-minimal g21 = refl , refl , refl , refl , refl
order-minimal g22 = refl , refl
order-minimal g23 = refl , refl , refl

-- 0 postulate.
