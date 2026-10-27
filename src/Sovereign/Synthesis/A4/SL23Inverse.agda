{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.SL23Inverse
--
-- **SL(2,F₃) 的逆 + 双侧逆律 + 共轭不变性（⇒ 类函数性质）**
--
-- `CharTable2A4` 的类表 `classOf2A4` 是"共轭类的计算序"结果，但当时**没有**
-- 证明它是共轭不变的——因为库里没有 SL23 的逆。本文件补齐：
--
--   §1 `invSL : SL23 → SL23`          24 案显式表（由 Cayley 表逐点解出）
--   §2 `invSL-adj`                    24 案：invSL 就是伴随矩阵（det = 1 的逆）
--   §3 双侧逆律 invSL-left / -right   各 24 案 refl
--   §4 `invSL-invol`                  24 案：对合
--   §5 共轭不变性 `classConj`          24 行 × 24 案 = 576 对
--   §6 类函数性质：7 个特征标**自动**共轭不变（由 §5 用 cong 搬运，不重算）
--
-- 有了 §6，"特征标是类函数"从数值观察变成定理；这是 `CharTable2A4` §10(c) 的闭合。
--
-- 未做（如实列出）：
--   · `inv-unique : x ⊗ y ≡ g6 → y ≡ invSL x` 与反同态 `invSL (x ⊗ y) ≡ invSL y ⊗ invSL x`
--     需要 SL23 的**结合律/单位律**（库里只有 Cayley 表，没有 `⊗-assoc`），
--     需另做 576 + 24 案；本文件的逆律只用逐点 refl，不依赖结合律。
--
-- 0 postulate / 0 hole；全枚举，零浮点。
module Sovereign.Synthesis.A4.SL23Inverse where

import Sovereign.Synthesis.A4.A4Group as A4G
open A4G using (A4)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Sovereign.Algebra.LinearAlgebra.Matrix2 using (Mat2)
open import Sovereign.Synthesis.Representation.Matrix2Inverse using (adj)
open import Sovereign.Synthesis.Representation.SL23Cayley using (_⊗_; toMat)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23)
open import Sovereign.Synthesis.A4.CharTable2A4
  using (Irr; charOf; classOf2A4)

--------------------------------------------------------------------------------
-- §1 逆元表（24 案）
--
--   由 Cayley 表逐点解出：invSL g = 唯一使 g ⊗ invSL g ≡ g6 的元素。
--   观察：g6 = I 自逆、g15 = −I 自逆，其余成对互换（g0↔g3、g1↔g13、…）。
--------------------------------------------------------------------------------

invSL : SL23 → SL23
invSL g0  = g3
invSL g1  = g13
invSL g2  = g22
invSL g3  = g0
invSL g4  = g11
invSL g5  = g20
invSL g6  = g6
invSL g7  = g8
invSL g8  = g7
invSL g9  = g12
invSL g10 = g23
invSL g11 = g4
invSL g12 = g9
invSL g13 = g1
invSL g14 = g19
invSL g15 = g15
invSL g16 = g17
invSL g17 = g16
invSL g18 = g21
invSL g19 = g14
invSL g20 = g5
invSL g21 = g18
invSL g22 = g2
invSL g23 = g10

--------------------------------------------------------------------------------
-- §2 逆的代数身份：invSL 就是伴随矩阵（det = 1 ⇒ 伴随即逆）
--
--   这条把 §1 的表钉在已有的代数构造上（Matrix2Inverse 的 adj），
--   说明它不是为了凑逆律而编的数据。
--------------------------------------------------------------------------------

invSL-adj : ∀ (x : SL23) → toMat (invSL x) ≡ adj (toMat x)
invSL-adj g0  = refl
invSL-adj g1  = refl
invSL-adj g2  = refl
invSL-adj g3  = refl
invSL-adj g4  = refl
invSL-adj g5  = refl
invSL-adj g6  = refl
invSL-adj g7  = refl
invSL-adj g8  = refl
invSL-adj g9  = refl
invSL-adj g10 = refl
invSL-adj g11 = refl
invSL-adj g12 = refl
invSL-adj g13 = refl
invSL-adj g14 = refl
invSL-adj g15 = refl
invSL-adj g16 = refl
invSL-adj g17 = refl
invSL-adj g18 = refl
invSL-adj g19 = refl
invSL-adj g20 = refl
invSL-adj g21 = refl
invSL-adj g22 = refl
invSL-adj g23 = refl

--------------------------------------------------------------------------------
-- §3 双侧逆律（各 24 案 refl）
--------------------------------------------------------------------------------

invSL-left : ∀ (x : SL23) → invSL x ⊗ x ≡ g6
invSL-left g0  = refl
invSL-left g1  = refl
invSL-left g2  = refl
invSL-left g3  = refl
invSL-left g4  = refl
invSL-left g5  = refl
invSL-left g6  = refl
invSL-left g7  = refl
invSL-left g8  = refl
invSL-left g9  = refl
invSL-left g10 = refl
invSL-left g11 = refl
invSL-left g12 = refl
invSL-left g13 = refl
invSL-left g14 = refl
invSL-left g15 = refl
invSL-left g16 = refl
invSL-left g17 = refl
invSL-left g18 = refl
invSL-left g19 = refl
invSL-left g20 = refl
invSL-left g21 = refl
invSL-left g22 = refl
invSL-left g23 = refl

invSL-right : ∀ (x : SL23) → x ⊗ invSL x ≡ g6
invSL-right g0  = refl
invSL-right g1  = refl
invSL-right g2  = refl
invSL-right g3  = refl
invSL-right g4  = refl
invSL-right g5  = refl
invSL-right g6  = refl
invSL-right g7  = refl
invSL-right g8  = refl
invSL-right g9  = refl
invSL-right g10 = refl
invSL-right g11 = refl
invSL-right g12 = refl
invSL-right g13 = refl
invSL-right g14 = refl
invSL-right g15 = refl
invSL-right g16 = refl
invSL-right g17 = refl
invSL-right g18 = refl
invSL-right g19 = refl
invSL-right g20 = refl
invSL-right g21 = refl
invSL-right g22 = refl
invSL-right g23 = refl

--------------------------------------------------------------------------------
-- §4 对合（24 案 refl）
--------------------------------------------------------------------------------

invSL-invol : ∀ (x : SL23) → invSL (invSL x) ≡ x
invSL-invol g0  = refl
invSL-invol g1  = refl
invSL-invol g2  = refl
invSL-invol g3  = refl
invSL-invol g4  = refl
invSL-invol g5  = refl
invSL-invol g6  = refl
invSL-invol g7  = refl
invSL-invol g8  = refl
invSL-invol g9  = refl
invSL-invol g10 = refl
invSL-invol g11 = refl
invSL-invol g12 = refl
invSL-invol g13 = refl
invSL-invol g14 = refl
invSL-invol g15 = refl
invSL-invol g16 = refl
invSL-invol g17 = refl
invSL-invol g18 = refl
invSL-invol g19 = refl
invSL-invol g20 = refl
invSL-invol g21 = refl
invSL-invol g22 = refl
invSL-invol g23 = refl

--------------------------------------------------------------------------------
-- §5 共轭不变性：classOf2A4 (h·g·h⁻¹) ≡ classOf2A4 g
--
--   24 个行引理（每个 ∀ h，24 案），共 576 对。
--   这正是 `CharTable2A4` 类表能当"共轭类"用的依据。
--------------------------------------------------------------------------------

classConj-g0 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g0) ⊗ invSL h) ≡ classOf2A4 g0
classConj-g0 g0  = refl
classConj-g0 g1  = refl
classConj-g0 g2  = refl
classConj-g0 g3  = refl
classConj-g0 g4  = refl
classConj-g0 g5  = refl
classConj-g0 g6  = refl
classConj-g0 g7  = refl
classConj-g0 g8  = refl
classConj-g0 g9  = refl
classConj-g0 g10 = refl
classConj-g0 g11 = refl
classConj-g0 g12 = refl
classConj-g0 g13 = refl
classConj-g0 g14 = refl
classConj-g0 g15 = refl
classConj-g0 g16 = refl
classConj-g0 g17 = refl
classConj-g0 g18 = refl
classConj-g0 g19 = refl
classConj-g0 g20 = refl
classConj-g0 g21 = refl
classConj-g0 g22 = refl
classConj-g0 g23 = refl

classConj-g1 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g1) ⊗ invSL h) ≡ classOf2A4 g1
classConj-g1 g0  = refl
classConj-g1 g1  = refl
classConj-g1 g2  = refl
classConj-g1 g3  = refl
classConj-g1 g4  = refl
classConj-g1 g5  = refl
classConj-g1 g6  = refl
classConj-g1 g7  = refl
classConj-g1 g8  = refl
classConj-g1 g9  = refl
classConj-g1 g10 = refl
classConj-g1 g11 = refl
classConj-g1 g12 = refl
classConj-g1 g13 = refl
classConj-g1 g14 = refl
classConj-g1 g15 = refl
classConj-g1 g16 = refl
classConj-g1 g17 = refl
classConj-g1 g18 = refl
classConj-g1 g19 = refl
classConj-g1 g20 = refl
classConj-g1 g21 = refl
classConj-g1 g22 = refl
classConj-g1 g23 = refl

classConj-g2 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g2) ⊗ invSL h) ≡ classOf2A4 g2
classConj-g2 g0  = refl
classConj-g2 g1  = refl
classConj-g2 g2  = refl
classConj-g2 g3  = refl
classConj-g2 g4  = refl
classConj-g2 g5  = refl
classConj-g2 g6  = refl
classConj-g2 g7  = refl
classConj-g2 g8  = refl
classConj-g2 g9  = refl
classConj-g2 g10 = refl
classConj-g2 g11 = refl
classConj-g2 g12 = refl
classConj-g2 g13 = refl
classConj-g2 g14 = refl
classConj-g2 g15 = refl
classConj-g2 g16 = refl
classConj-g2 g17 = refl
classConj-g2 g18 = refl
classConj-g2 g19 = refl
classConj-g2 g20 = refl
classConj-g2 g21 = refl
classConj-g2 g22 = refl
classConj-g2 g23 = refl

classConj-g3 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g3) ⊗ invSL h) ≡ classOf2A4 g3
classConj-g3 g0  = refl
classConj-g3 g1  = refl
classConj-g3 g2  = refl
classConj-g3 g3  = refl
classConj-g3 g4  = refl
classConj-g3 g5  = refl
classConj-g3 g6  = refl
classConj-g3 g7  = refl
classConj-g3 g8  = refl
classConj-g3 g9  = refl
classConj-g3 g10 = refl
classConj-g3 g11 = refl
classConj-g3 g12 = refl
classConj-g3 g13 = refl
classConj-g3 g14 = refl
classConj-g3 g15 = refl
classConj-g3 g16 = refl
classConj-g3 g17 = refl
classConj-g3 g18 = refl
classConj-g3 g19 = refl
classConj-g3 g20 = refl
classConj-g3 g21 = refl
classConj-g3 g22 = refl
classConj-g3 g23 = refl

classConj-g4 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g4) ⊗ invSL h) ≡ classOf2A4 g4
classConj-g4 g0  = refl
classConj-g4 g1  = refl
classConj-g4 g2  = refl
classConj-g4 g3  = refl
classConj-g4 g4  = refl
classConj-g4 g5  = refl
classConj-g4 g6  = refl
classConj-g4 g7  = refl
classConj-g4 g8  = refl
classConj-g4 g9  = refl
classConj-g4 g10 = refl
classConj-g4 g11 = refl
classConj-g4 g12 = refl
classConj-g4 g13 = refl
classConj-g4 g14 = refl
classConj-g4 g15 = refl
classConj-g4 g16 = refl
classConj-g4 g17 = refl
classConj-g4 g18 = refl
classConj-g4 g19 = refl
classConj-g4 g20 = refl
classConj-g4 g21 = refl
classConj-g4 g22 = refl
classConj-g4 g23 = refl

classConj-g5 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g5) ⊗ invSL h) ≡ classOf2A4 g5
classConj-g5 g0  = refl
classConj-g5 g1  = refl
classConj-g5 g2  = refl
classConj-g5 g3  = refl
classConj-g5 g4  = refl
classConj-g5 g5  = refl
classConj-g5 g6  = refl
classConj-g5 g7  = refl
classConj-g5 g8  = refl
classConj-g5 g9  = refl
classConj-g5 g10 = refl
classConj-g5 g11 = refl
classConj-g5 g12 = refl
classConj-g5 g13 = refl
classConj-g5 g14 = refl
classConj-g5 g15 = refl
classConj-g5 g16 = refl
classConj-g5 g17 = refl
classConj-g5 g18 = refl
classConj-g5 g19 = refl
classConj-g5 g20 = refl
classConj-g5 g21 = refl
classConj-g5 g22 = refl
classConj-g5 g23 = refl

classConj-g6 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g6) ⊗ invSL h) ≡ classOf2A4 g6
classConj-g6 g0  = refl
classConj-g6 g1  = refl
classConj-g6 g2  = refl
classConj-g6 g3  = refl
classConj-g6 g4  = refl
classConj-g6 g5  = refl
classConj-g6 g6  = refl
classConj-g6 g7  = refl
classConj-g6 g8  = refl
classConj-g6 g9  = refl
classConj-g6 g10 = refl
classConj-g6 g11 = refl
classConj-g6 g12 = refl
classConj-g6 g13 = refl
classConj-g6 g14 = refl
classConj-g6 g15 = refl
classConj-g6 g16 = refl
classConj-g6 g17 = refl
classConj-g6 g18 = refl
classConj-g6 g19 = refl
classConj-g6 g20 = refl
classConj-g6 g21 = refl
classConj-g6 g22 = refl
classConj-g6 g23 = refl

classConj-g7 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g7) ⊗ invSL h) ≡ classOf2A4 g7
classConj-g7 g0  = refl
classConj-g7 g1  = refl
classConj-g7 g2  = refl
classConj-g7 g3  = refl
classConj-g7 g4  = refl
classConj-g7 g5  = refl
classConj-g7 g6  = refl
classConj-g7 g7  = refl
classConj-g7 g8  = refl
classConj-g7 g9  = refl
classConj-g7 g10 = refl
classConj-g7 g11 = refl
classConj-g7 g12 = refl
classConj-g7 g13 = refl
classConj-g7 g14 = refl
classConj-g7 g15 = refl
classConj-g7 g16 = refl
classConj-g7 g17 = refl
classConj-g7 g18 = refl
classConj-g7 g19 = refl
classConj-g7 g20 = refl
classConj-g7 g21 = refl
classConj-g7 g22 = refl
classConj-g7 g23 = refl

classConj-g8 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g8) ⊗ invSL h) ≡ classOf2A4 g8
classConj-g8 g0  = refl
classConj-g8 g1  = refl
classConj-g8 g2  = refl
classConj-g8 g3  = refl
classConj-g8 g4  = refl
classConj-g8 g5  = refl
classConj-g8 g6  = refl
classConj-g8 g7  = refl
classConj-g8 g8  = refl
classConj-g8 g9  = refl
classConj-g8 g10 = refl
classConj-g8 g11 = refl
classConj-g8 g12 = refl
classConj-g8 g13 = refl
classConj-g8 g14 = refl
classConj-g8 g15 = refl
classConj-g8 g16 = refl
classConj-g8 g17 = refl
classConj-g8 g18 = refl
classConj-g8 g19 = refl
classConj-g8 g20 = refl
classConj-g8 g21 = refl
classConj-g8 g22 = refl
classConj-g8 g23 = refl

classConj-g9 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g9) ⊗ invSL h) ≡ classOf2A4 g9
classConj-g9 g0  = refl
classConj-g9 g1  = refl
classConj-g9 g2  = refl
classConj-g9 g3  = refl
classConj-g9 g4  = refl
classConj-g9 g5  = refl
classConj-g9 g6  = refl
classConj-g9 g7  = refl
classConj-g9 g8  = refl
classConj-g9 g9  = refl
classConj-g9 g10 = refl
classConj-g9 g11 = refl
classConj-g9 g12 = refl
classConj-g9 g13 = refl
classConj-g9 g14 = refl
classConj-g9 g15 = refl
classConj-g9 g16 = refl
classConj-g9 g17 = refl
classConj-g9 g18 = refl
classConj-g9 g19 = refl
classConj-g9 g20 = refl
classConj-g9 g21 = refl
classConj-g9 g22 = refl
classConj-g9 g23 = refl

classConj-g10 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g10) ⊗ invSL h) ≡ classOf2A4 g10
classConj-g10 g0  = refl
classConj-g10 g1  = refl
classConj-g10 g2  = refl
classConj-g10 g3  = refl
classConj-g10 g4  = refl
classConj-g10 g5  = refl
classConj-g10 g6  = refl
classConj-g10 g7  = refl
classConj-g10 g8  = refl
classConj-g10 g9  = refl
classConj-g10 g10 = refl
classConj-g10 g11 = refl
classConj-g10 g12 = refl
classConj-g10 g13 = refl
classConj-g10 g14 = refl
classConj-g10 g15 = refl
classConj-g10 g16 = refl
classConj-g10 g17 = refl
classConj-g10 g18 = refl
classConj-g10 g19 = refl
classConj-g10 g20 = refl
classConj-g10 g21 = refl
classConj-g10 g22 = refl
classConj-g10 g23 = refl

classConj-g11 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g11) ⊗ invSL h) ≡ classOf2A4 g11
classConj-g11 g0  = refl
classConj-g11 g1  = refl
classConj-g11 g2  = refl
classConj-g11 g3  = refl
classConj-g11 g4  = refl
classConj-g11 g5  = refl
classConj-g11 g6  = refl
classConj-g11 g7  = refl
classConj-g11 g8  = refl
classConj-g11 g9  = refl
classConj-g11 g10 = refl
classConj-g11 g11 = refl
classConj-g11 g12 = refl
classConj-g11 g13 = refl
classConj-g11 g14 = refl
classConj-g11 g15 = refl
classConj-g11 g16 = refl
classConj-g11 g17 = refl
classConj-g11 g18 = refl
classConj-g11 g19 = refl
classConj-g11 g20 = refl
classConj-g11 g21 = refl
classConj-g11 g22 = refl
classConj-g11 g23 = refl

classConj-g12 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g12) ⊗ invSL h) ≡ classOf2A4 g12
classConj-g12 g0  = refl
classConj-g12 g1  = refl
classConj-g12 g2  = refl
classConj-g12 g3  = refl
classConj-g12 g4  = refl
classConj-g12 g5  = refl
classConj-g12 g6  = refl
classConj-g12 g7  = refl
classConj-g12 g8  = refl
classConj-g12 g9  = refl
classConj-g12 g10 = refl
classConj-g12 g11 = refl
classConj-g12 g12 = refl
classConj-g12 g13 = refl
classConj-g12 g14 = refl
classConj-g12 g15 = refl
classConj-g12 g16 = refl
classConj-g12 g17 = refl
classConj-g12 g18 = refl
classConj-g12 g19 = refl
classConj-g12 g20 = refl
classConj-g12 g21 = refl
classConj-g12 g22 = refl
classConj-g12 g23 = refl

classConj-g13 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g13) ⊗ invSL h) ≡ classOf2A4 g13
classConj-g13 g0  = refl
classConj-g13 g1  = refl
classConj-g13 g2  = refl
classConj-g13 g3  = refl
classConj-g13 g4  = refl
classConj-g13 g5  = refl
classConj-g13 g6  = refl
classConj-g13 g7  = refl
classConj-g13 g8  = refl
classConj-g13 g9  = refl
classConj-g13 g10 = refl
classConj-g13 g11 = refl
classConj-g13 g12 = refl
classConj-g13 g13 = refl
classConj-g13 g14 = refl
classConj-g13 g15 = refl
classConj-g13 g16 = refl
classConj-g13 g17 = refl
classConj-g13 g18 = refl
classConj-g13 g19 = refl
classConj-g13 g20 = refl
classConj-g13 g21 = refl
classConj-g13 g22 = refl
classConj-g13 g23 = refl

classConj-g14 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g14) ⊗ invSL h) ≡ classOf2A4 g14
classConj-g14 g0  = refl
classConj-g14 g1  = refl
classConj-g14 g2  = refl
classConj-g14 g3  = refl
classConj-g14 g4  = refl
classConj-g14 g5  = refl
classConj-g14 g6  = refl
classConj-g14 g7  = refl
classConj-g14 g8  = refl
classConj-g14 g9  = refl
classConj-g14 g10 = refl
classConj-g14 g11 = refl
classConj-g14 g12 = refl
classConj-g14 g13 = refl
classConj-g14 g14 = refl
classConj-g14 g15 = refl
classConj-g14 g16 = refl
classConj-g14 g17 = refl
classConj-g14 g18 = refl
classConj-g14 g19 = refl
classConj-g14 g20 = refl
classConj-g14 g21 = refl
classConj-g14 g22 = refl
classConj-g14 g23 = refl

classConj-g15 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g15) ⊗ invSL h) ≡ classOf2A4 g15
classConj-g15 g0  = refl
classConj-g15 g1  = refl
classConj-g15 g2  = refl
classConj-g15 g3  = refl
classConj-g15 g4  = refl
classConj-g15 g5  = refl
classConj-g15 g6  = refl
classConj-g15 g7  = refl
classConj-g15 g8  = refl
classConj-g15 g9  = refl
classConj-g15 g10 = refl
classConj-g15 g11 = refl
classConj-g15 g12 = refl
classConj-g15 g13 = refl
classConj-g15 g14 = refl
classConj-g15 g15 = refl
classConj-g15 g16 = refl
classConj-g15 g17 = refl
classConj-g15 g18 = refl
classConj-g15 g19 = refl
classConj-g15 g20 = refl
classConj-g15 g21 = refl
classConj-g15 g22 = refl
classConj-g15 g23 = refl

classConj-g16 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g16) ⊗ invSL h) ≡ classOf2A4 g16
classConj-g16 g0  = refl
classConj-g16 g1  = refl
classConj-g16 g2  = refl
classConj-g16 g3  = refl
classConj-g16 g4  = refl
classConj-g16 g5  = refl
classConj-g16 g6  = refl
classConj-g16 g7  = refl
classConj-g16 g8  = refl
classConj-g16 g9  = refl
classConj-g16 g10 = refl
classConj-g16 g11 = refl
classConj-g16 g12 = refl
classConj-g16 g13 = refl
classConj-g16 g14 = refl
classConj-g16 g15 = refl
classConj-g16 g16 = refl
classConj-g16 g17 = refl
classConj-g16 g18 = refl
classConj-g16 g19 = refl
classConj-g16 g20 = refl
classConj-g16 g21 = refl
classConj-g16 g22 = refl
classConj-g16 g23 = refl

classConj-g17 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g17) ⊗ invSL h) ≡ classOf2A4 g17
classConj-g17 g0  = refl
classConj-g17 g1  = refl
classConj-g17 g2  = refl
classConj-g17 g3  = refl
classConj-g17 g4  = refl
classConj-g17 g5  = refl
classConj-g17 g6  = refl
classConj-g17 g7  = refl
classConj-g17 g8  = refl
classConj-g17 g9  = refl
classConj-g17 g10 = refl
classConj-g17 g11 = refl
classConj-g17 g12 = refl
classConj-g17 g13 = refl
classConj-g17 g14 = refl
classConj-g17 g15 = refl
classConj-g17 g16 = refl
classConj-g17 g17 = refl
classConj-g17 g18 = refl
classConj-g17 g19 = refl
classConj-g17 g20 = refl
classConj-g17 g21 = refl
classConj-g17 g22 = refl
classConj-g17 g23 = refl

classConj-g18 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g18) ⊗ invSL h) ≡ classOf2A4 g18
classConj-g18 g0  = refl
classConj-g18 g1  = refl
classConj-g18 g2  = refl
classConj-g18 g3  = refl
classConj-g18 g4  = refl
classConj-g18 g5  = refl
classConj-g18 g6  = refl
classConj-g18 g7  = refl
classConj-g18 g8  = refl
classConj-g18 g9  = refl
classConj-g18 g10 = refl
classConj-g18 g11 = refl
classConj-g18 g12 = refl
classConj-g18 g13 = refl
classConj-g18 g14 = refl
classConj-g18 g15 = refl
classConj-g18 g16 = refl
classConj-g18 g17 = refl
classConj-g18 g18 = refl
classConj-g18 g19 = refl
classConj-g18 g20 = refl
classConj-g18 g21 = refl
classConj-g18 g22 = refl
classConj-g18 g23 = refl

classConj-g19 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g19) ⊗ invSL h) ≡ classOf2A4 g19
classConj-g19 g0  = refl
classConj-g19 g1  = refl
classConj-g19 g2  = refl
classConj-g19 g3  = refl
classConj-g19 g4  = refl
classConj-g19 g5  = refl
classConj-g19 g6  = refl
classConj-g19 g7  = refl
classConj-g19 g8  = refl
classConj-g19 g9  = refl
classConj-g19 g10 = refl
classConj-g19 g11 = refl
classConj-g19 g12 = refl
classConj-g19 g13 = refl
classConj-g19 g14 = refl
classConj-g19 g15 = refl
classConj-g19 g16 = refl
classConj-g19 g17 = refl
classConj-g19 g18 = refl
classConj-g19 g19 = refl
classConj-g19 g20 = refl
classConj-g19 g21 = refl
classConj-g19 g22 = refl
classConj-g19 g23 = refl

classConj-g20 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g20) ⊗ invSL h) ≡ classOf2A4 g20
classConj-g20 g0  = refl
classConj-g20 g1  = refl
classConj-g20 g2  = refl
classConj-g20 g3  = refl
classConj-g20 g4  = refl
classConj-g20 g5  = refl
classConj-g20 g6  = refl
classConj-g20 g7  = refl
classConj-g20 g8  = refl
classConj-g20 g9  = refl
classConj-g20 g10 = refl
classConj-g20 g11 = refl
classConj-g20 g12 = refl
classConj-g20 g13 = refl
classConj-g20 g14 = refl
classConj-g20 g15 = refl
classConj-g20 g16 = refl
classConj-g20 g17 = refl
classConj-g20 g18 = refl
classConj-g20 g19 = refl
classConj-g20 g20 = refl
classConj-g20 g21 = refl
classConj-g20 g22 = refl
classConj-g20 g23 = refl

classConj-g21 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g21) ⊗ invSL h) ≡ classOf2A4 g21
classConj-g21 g0  = refl
classConj-g21 g1  = refl
classConj-g21 g2  = refl
classConj-g21 g3  = refl
classConj-g21 g4  = refl
classConj-g21 g5  = refl
classConj-g21 g6  = refl
classConj-g21 g7  = refl
classConj-g21 g8  = refl
classConj-g21 g9  = refl
classConj-g21 g10 = refl
classConj-g21 g11 = refl
classConj-g21 g12 = refl
classConj-g21 g13 = refl
classConj-g21 g14 = refl
classConj-g21 g15 = refl
classConj-g21 g16 = refl
classConj-g21 g17 = refl
classConj-g21 g18 = refl
classConj-g21 g19 = refl
classConj-g21 g20 = refl
classConj-g21 g21 = refl
classConj-g21 g22 = refl
classConj-g21 g23 = refl

classConj-g22 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g22) ⊗ invSL h) ≡ classOf2A4 g22
classConj-g22 g0  = refl
classConj-g22 g1  = refl
classConj-g22 g2  = refl
classConj-g22 g3  = refl
classConj-g22 g4  = refl
classConj-g22 g5  = refl
classConj-g22 g6  = refl
classConj-g22 g7  = refl
classConj-g22 g8  = refl
classConj-g22 g9  = refl
classConj-g22 g10 = refl
classConj-g22 g11 = refl
classConj-g22 g12 = refl
classConj-g22 g13 = refl
classConj-g22 g14 = refl
classConj-g22 g15 = refl
classConj-g22 g16 = refl
classConj-g22 g17 = refl
classConj-g22 g18 = refl
classConj-g22 g19 = refl
classConj-g22 g20 = refl
classConj-g22 g21 = refl
classConj-g22 g22 = refl
classConj-g22 g23 = refl

classConj-g23 : ∀ (h : SL23) → classOf2A4 ((h ⊗ g23) ⊗ invSL h) ≡ classOf2A4 g23
classConj-g23 g0  = refl
classConj-g23 g1  = refl
classConj-g23 g2  = refl
classConj-g23 g3  = refl
classConj-g23 g4  = refl
classConj-g23 g5  = refl
classConj-g23 g6  = refl
classConj-g23 g7  = refl
classConj-g23 g8  = refl
classConj-g23 g9  = refl
classConj-g23 g10 = refl
classConj-g23 g11 = refl
classConj-g23 g12 = refl
classConj-g23 g13 = refl
classConj-g23 g14 = refl
classConj-g23 g15 = refl
classConj-g23 g16 = refl
classConj-g23 g17 = refl
classConj-g23 g18 = refl
classConj-g23 g19 = refl
classConj-g23 g20 = refl
classConj-g23 g21 = refl
classConj-g23 g22 = refl
classConj-g23 g23 = refl

classConj : ∀ (g h : SL23) → classOf2A4 ((h ⊗ g) ⊗ invSL h) ≡ classOf2A4 g
classConj g0  = classConj-g0
classConj g1  = classConj-g1
classConj g2  = classConj-g2
classConj g3  = classConj-g3
classConj g4  = classConj-g4
classConj g5  = classConj-g5
classConj g6  = classConj-g6
classConj g7  = classConj-g7
classConj g8  = classConj-g8
classConj g9  = classConj-g9
classConj g10 = classConj-g10
classConj g11 = classConj-g11
classConj g12 = classConj-g12
classConj g13 = classConj-g13
classConj g14 = classConj-g14
classConj g15 = classConj-g15
classConj g16 = classConj-g16
classConj g17 = classConj-g17
classConj g18 = classConj-g18
classConj g19 = classConj-g19
classConj g20 = classConj-g20
classConj g21 = classConj-g21
classConj g22 = classConj-g22
classConj g23 = classConj-g23

-- 左共轭形式（由右形式 + 对合）：h⁻¹·g·h
classConj-left : ∀ (g h : SL23) → classOf2A4 ((invSL h ⊗ g) ⊗ h) ≡ classOf2A4 g
classConj-left g h =
  trans (cong (λ k → classOf2A4 ((invSL h ⊗ g) ⊗ k)) (sym (invSL-invol h)))
        (classConj g (invSL h))

--------------------------------------------------------------------------------
-- §6 类函数性质：7 个特征标全部共轭不变
--
--   χ 定义为 `charOf r ∘ classOf2A4`，所以只需 classOf2A4 的共轭不变性；
--   这一步对 7 行**同时**成立，不需要逐行重算。
--------------------------------------------------------------------------------

charClassFunction : ∀ (r : Irr) (g h : SL23)
                  → charOf r (classOf2A4 ((h ⊗ g) ⊗ invSL h)) ≡ charOf r (classOf2A4 g)
charClassFunction r g h = cong (charOf r) (classConj g h)

--------------------------------------------------------------------------------
-- §7 打包
--------------------------------------------------------------------------------

record SL23InverseData : Set where
  field
    inv            : SL23 → SL23
    inv-adj        : ∀ (x : SL23) → toMat (inv x) ≡ adj (toMat x)
    inv-left-law   : ∀ (x : SL23) → inv x ⊗ x ≡ g6
    inv-right-law  : ∀ (x : SL23) → x ⊗ inv x ≡ g6
    inv-involution : ∀ (x : SL23) → inv (inv x) ≡ x
    class-conj     : ∀ (g h : SL23) → classOf2A4 ((h ⊗ g) ⊗ inv h) ≡ classOf2A4 g
    class-conj-left : ∀ (g h : SL23) → classOf2A4 ((inv h ⊗ g) ⊗ h) ≡ classOf2A4 g
    char-class     : ∀ (r : Irr) (g h : SL23)
                   → charOf r (classOf2A4 ((h ⊗ g) ⊗ inv h)) ≡ charOf r (classOf2A4 g)

sl23InverseData : SL23InverseData
sl23InverseData = record
  { inv             = invSL
  ; inv-adj         = invSL-adj
  ; inv-left-law    = invSL-left
  ; inv-right-law   = invSL-right
  ; inv-involution  = invSL-invol
  ; class-conj      = classConj
  ; class-conj-left = classConj-left
  ; char-class      = charClassFunction
  }
