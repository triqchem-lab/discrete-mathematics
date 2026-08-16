{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.SL23Trace
-- 矩阵 → 迹 → 特征标: SL(2,3) 定义表示的显式迹 (0 postulate)
--
-- 表示论的源头是矩阵: 特征标是矩阵的迹。本模块显式证明:
--   对每个 g ∈ SL(2,3), traceMat(toMat g) ≡ classTrace(classOf g)  (迹 mod 3)
-- 结合 BinaryTetrahedralDefiningRep 的 chi2FromRep (Brauer 提升 lift ∘ order),
-- 得到完整链: 矩阵 → 迹(mod3) + 阶(特征值结构) → χ₂。
--
-- 注意: SL(2,3) 的定义表示是 GF(3) 上的 det=1 矩阵 (无分母), 这是矩阵构造的源头;
-- 其在特征 0 的忠实二维表示需 1/2 (「半元素」), 故 Z[ω,i] 整环上无忠实二维矩阵表示,
-- 迹含 ω 的 χ₂′/χ₂″ 由张量积 χ₂ ⊗ {χ₁′,χ₁″} 导出 (见 BinaryTetrahedralTwoDimTensors)。

module Sovereign.Structology.SL23Trace where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Structology.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23; classOf)
open import Sovereign.Structology.SL23Cayley using (Mat2; mat2; toMat; add3)

--------------------------------------------------------------------------------
-- §1. 迹 (mod 3)
--------------------------------------------------------------------------------

traceMat : Mat2 → Fin 3
traceMat (mat2 a b c d) = add3 a d

-- 每个共轭类的迹 (mod 3): [Id, -I, 3a, 3b, 6a, 6b, 4a] → [2,1,2,2,1,1,0]
classTrace : Fin 7 → Fin 3
classTrace zero = suc (suc zero)
classTrace (suc zero) = suc zero
classTrace (suc (suc zero)) = suc (suc zero)
classTrace (suc (suc (suc zero))) = suc (suc zero)
classTrace (suc (suc (suc (suc zero)))) = suc zero
classTrace (suc (suc (suc (suc (suc zero))))) = suc zero
classTrace (suc (suc (suc (suc (suc (suc zero)))))) = zero

--------------------------------------------------------------------------------
-- §2. 主定理: 矩阵迹 = 类迹 (24 refl)
--------------------------------------------------------------------------------

trace-correct : ∀ (g : SL23) → traceMat (toMat g) ≡ classTrace (classOf g)
trace-correct g0 = refl
trace-correct g1 = refl
trace-correct g2 = refl
trace-correct g3 = refl
trace-correct g4 = refl
trace-correct g5 = refl
trace-correct g6 = refl
trace-correct g7 = refl
trace-correct g8 = refl
trace-correct g9 = refl
trace-correct g10 = refl
trace-correct g11 = refl
trace-correct g12 = refl
trace-correct g13 = refl
trace-correct g14 = refl
trace-correct g15 = refl
trace-correct g16 = refl
trace-correct g17 = refl
trace-correct g18 = refl
trace-correct g19 = refl
trace-correct g20 = refl
trace-correct g21 = refl
trace-correct g22 = refl
trace-correct g23 = refl

-- 0 postulate.
