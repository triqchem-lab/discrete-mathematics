{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.SL23Group
--
-- **SL(2,F₃) 的群律**：结合律、单位律、消去律、逆唯一、反同态
--
-- 为什么需要：`SL23Inverse` 只给了逐点的双侧逆律（24 案 refl），没给结合律——
-- 而结合律需要把 SL23 的乘法表与**矩阵乘法**接上。本文件的策略是
--   「矩阵模型 + toMat 的单射性」，
-- 单射性不再靠 576 对枚举，而是造一个**反演函数** `fromMat`：
--
--   fromMat  : Mat2 → SL23        24 个模式 + 兜底（非像上的值一律给 g6）
--   fromMat-toMat : fromMat (toMat x) ≡ x            24 案 refl
--   toMat-inj : toMat x ≡ toMat y → x ≡ y            由"有左逆 ⇒ 单射"（3 行）
--
-- 于是结合律 = toMat-hom + `Fin3Semiring.mat-assoc` + toMat-inj，**不需要 24³ 枚举**。
--
-- 之后：单位律（各 24 案 refl）、消去律、`inv-unique`、反同态
--     invSL (x ⊗ y) ≡ invSL y ⊗ invSL x
-- 全部由群律代数推出（不再是查表）。
--
-- 0 postulate / 0 hole；枚举部分只有 fromMat/单位律的 24 案表。
module Sovereign.Synthesis.A4.SL23Group where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open ≡-Reasoning

open import Sovereign.Algebra.LinearAlgebra.Matrix2 using (mkMat2)
open import Sovereign.Synthesis.Representation.Fin3Semiring using (mat-assoc)
open import Sovereign.Synthesis.Representation.SL23Cayley
  using (_⊗_; Mat2; toMat; toMat-hom; mulMat2)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep
  using (SL23; g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11
        ; g12; g13; g14; g15; g16; g17; g18; g19; g20; g21; g22; g23)
open import Sovereign.Synthesis.A4.SL23Inverse
  using ( invSL; invSL-left; invSL-right )

--------------------------------------------------------------------------------
-- §1 反演函数：Mat2 → SL23（在 24 个像上还原，别处给 g6）
--
--   它只需要"在这 24 个点上是左逆"，由此得到 toMat 的单射性。
--------------------------------------------------------------------------------

fromMat : Mat2 → SL23
fromMat (mkMat2 zero (suc zero) (suc (suc zero)) zero) = g0
fromMat (mkMat2 zero (suc zero) (suc (suc zero)) (suc zero)) = g1
fromMat (mkMat2 zero (suc zero) (suc (suc zero)) (suc (suc zero))) = g2
fromMat (mkMat2 zero (suc (suc zero)) (suc zero) zero) = g3
fromMat (mkMat2 zero (suc (suc zero)) (suc zero) (suc zero)) = g4
fromMat (mkMat2 zero (suc (suc zero)) (suc zero) (suc (suc zero))) = g5
fromMat (mkMat2 (suc zero) zero zero (suc zero)) = g6
fromMat (mkMat2 (suc zero) zero (suc zero) (suc zero)) = g7
fromMat (mkMat2 (suc zero) zero (suc (suc zero)) (suc zero)) = g8
fromMat (mkMat2 (suc zero) (suc zero) zero (suc zero)) = g9
fromMat (mkMat2 (suc zero) (suc zero) (suc zero) (suc (suc zero))) = g10
fromMat (mkMat2 (suc zero) (suc zero) (suc (suc zero)) zero) = g11
fromMat (mkMat2 (suc zero) (suc (suc zero)) zero (suc zero)) = g12
fromMat (mkMat2 (suc zero) (suc (suc zero)) (suc zero) zero) = g13
fromMat (mkMat2 (suc zero) (suc (suc zero)) (suc (suc zero)) (suc (suc zero))) = g14
fromMat (mkMat2 (suc (suc zero)) zero zero (suc (suc zero))) = g15
fromMat (mkMat2 (suc (suc zero)) zero (suc zero) (suc (suc zero))) = g16
fromMat (mkMat2 (suc (suc zero)) zero (suc (suc zero)) (suc (suc zero))) = g17
fromMat (mkMat2 (suc (suc zero)) (suc zero) zero (suc (suc zero))) = g18
fromMat (mkMat2 (suc (suc zero)) (suc zero) (suc zero) (suc zero)) = g19
fromMat (mkMat2 (suc (suc zero)) (suc zero) (suc (suc zero)) zero) = g20
fromMat (mkMat2 (suc (suc zero)) (suc (suc zero)) zero (suc (suc zero))) = g21
fromMat (mkMat2 (suc (suc zero)) (suc (suc zero)) (suc zero) zero) = g22
fromMat (mkMat2 (suc (suc zero)) (suc (suc zero)) (suc (suc zero)) (suc zero)) = g23
fromMat _ = g6

fromMat-toMat : ∀ (x : SL23) → fromMat (toMat x) ≡ x
fromMat-toMat g0  = refl
fromMat-toMat g1  = refl
fromMat-toMat g2  = refl
fromMat-toMat g3  = refl
fromMat-toMat g4  = refl
fromMat-toMat g5  = refl
fromMat-toMat g6  = refl
fromMat-toMat g7  = refl
fromMat-toMat g8  = refl
fromMat-toMat g9  = refl
fromMat-toMat g10 = refl
fromMat-toMat g11 = refl
fromMat-toMat g12 = refl
fromMat-toMat g13 = refl
fromMat-toMat g14 = refl
fromMat-toMat g15 = refl
fromMat-toMat g16 = refl
fromMat-toMat g17 = refl
fromMat-toMat g18 = refl
fromMat-toMat g19 = refl
fromMat-toMat g20 = refl
fromMat-toMat g21 = refl
fromMat-toMat g22 = refl
fromMat-toMat g23 = refl

-- | toMat 单射（有左逆 ⇒ 单射）
toMat-inj : ∀ (x y : SL23) → toMat x ≡ toMat y → x ≡ y
toMat-inj x y e =
  trans (sym (fromMat-toMat x)) (trans (cong fromMat e) (fromMat-toMat y))

--------------------------------------------------------------------------------
-- §2 结合律：矩阵模型的结合律沿单射搬回
--
--   (x·y)·z 与 x·(y·z) 的像相同（toMat-hom 两次 + mat-assoc + toMat-hom 两次），
--   由单射性即得相等。**不用 24³ 枚举。**
--------------------------------------------------------------------------------

⊗-assocSL : ∀ (x y z : SL23) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
⊗-assocSL x y z = toMat-inj ((x ⊗ y) ⊗ z) (x ⊗ (y ⊗ z)) (begin
    toMat ((x ⊗ y) ⊗ z)
  ≡⟨ toMat-hom (x ⊗ y) z ⟩
    mulMat2 (toMat (x ⊗ y)) (toMat z)
  ≡⟨ cong (λ m → mulMat2 m (toMat z)) (toMat-hom x y) ⟩
    mulMat2 (mulMat2 (toMat x) (toMat y)) (toMat z)
  ≡⟨ mat-assoc (toMat x) (toMat y) (toMat z) ⟩
    mulMat2 (toMat x) (mulMat2 (toMat y) (toMat z))
  ≡⟨ cong (mulMat2 (toMat x)) (sym (toMat-hom y z)) ⟩
    mulMat2 (toMat x) (toMat (y ⊗ z))
  ≡⟨ sym (toMat-hom x (y ⊗ z)) ⟩
    toMat (x ⊗ (y ⊗ z))
  ∎)

-- 非平凡性核查：SL23 非交换 ⇒ 结合律不是"反正都一样"的空洞陈述
⊗-noncomm : (g0 ⊗ g1) ≢ (g1 ⊗ g0)
⊗-noncomm = λ ()

--------------------------------------------------------------------------------
-- §3 单位律（各 24 案 refl；g6 = I）
--------------------------------------------------------------------------------

⊗-idˡ : ∀ (x : SL23) → g6 ⊗ x ≡ x
⊗-idˡ g0  = refl
⊗-idˡ g1  = refl
⊗-idˡ g2  = refl
⊗-idˡ g3  = refl
⊗-idˡ g4  = refl
⊗-idˡ g5  = refl
⊗-idˡ g6  = refl
⊗-idˡ g7  = refl
⊗-idˡ g8  = refl
⊗-idˡ g9  = refl
⊗-idˡ g10 = refl
⊗-idˡ g11 = refl
⊗-idˡ g12 = refl
⊗-idˡ g13 = refl
⊗-idˡ g14 = refl
⊗-idˡ g15 = refl
⊗-idˡ g16 = refl
⊗-idˡ g17 = refl
⊗-idˡ g18 = refl
⊗-idˡ g19 = refl
⊗-idˡ g20 = refl
⊗-idˡ g21 = refl
⊗-idˡ g22 = refl
⊗-idˡ g23 = refl

⊗-idʳ : ∀ (x : SL23) → x ⊗ g6 ≡ x
⊗-idʳ g0  = refl
⊗-idʳ g1  = refl
⊗-idʳ g2  = refl
⊗-idʳ g3  = refl
⊗-idʳ g4  = refl
⊗-idʳ g5  = refl
⊗-idʳ g6  = refl
⊗-idʳ g7  = refl
⊗-idʳ g8  = refl
⊗-idʳ g9  = refl
⊗-idʳ g10 = refl
⊗-idʳ g11 = refl
⊗-idʳ g12 = refl
⊗-idʳ g13 = refl
⊗-idʳ g14 = refl
⊗-idʳ g15 = refl
⊗-idʳ g16 = refl
⊗-idʳ g17 = refl
⊗-idʳ g18 = refl
⊗-idʳ g19 = refl
⊗-idʳ g20 = refl
⊗-idʳ g21 = refl
⊗-idʳ g22 = refl
⊗-idʳ g23 = refl

--------------------------------------------------------------------------------
-- §4 左消去律：x·y ≡ x·z ⇒ y ≡ z（群律的经典推论，走逆元）
--------------------------------------------------------------------------------

⊗-cancelˡ : ∀ (x y z : SL23) → x ⊗ y ≡ x ⊗ z → y ≡ z
⊗-cancelˡ x y z e = begin
    y
  ≡⟨ sym (⊗-idˡ y) ⟩
    g6 ⊗ y
  ≡⟨ cong (λ t → t ⊗ y) (sym (invSL-left x)) ⟩
    (invSL x ⊗ x) ⊗ y
  ≡⟨ ⊗-assocSL (invSL x) x y ⟩
    invSL x ⊗ (x ⊗ y)
  ≡⟨ cong (λ t → invSL x ⊗ t) e ⟩
    invSL x ⊗ (x ⊗ z)
  ≡⟨ sym (⊗-assocSL (invSL x) x z) ⟩
    (invSL x ⊗ x) ⊗ z
  ≡⟨ cong (λ t → t ⊗ z) (invSL-left x) ⟩
    g6 ⊗ z
  ≡⟨ ⊗-idˡ z ⟩
    z
  ∎

--------------------------------------------------------------------------------
-- §5 逆唯一：x·y ≡ e ⇒ y ≡ x⁻¹
--------------------------------------------------------------------------------

inv-unique : ∀ (x y : SL23) → x ⊗ y ≡ g6 → y ≡ invSL x
inv-unique x y e = begin
    y
  ≡⟨ sym (⊗-idˡ y) ⟩
    g6 ⊗ y
  ≡⟨ cong (λ t → t ⊗ y) (sym (invSL-left x)) ⟩
    (invSL x ⊗ x) ⊗ y
  ≡⟨ ⊗-assocSL (invSL x) x y ⟩
    invSL x ⊗ (x ⊗ y)
  ≡⟨ cong (λ t → invSL x ⊗ t) e ⟩
    invSL x ⊗ g6
  ≡⟨ ⊗-idʳ (invSL x) ⟩
    invSL x
  ∎

--------------------------------------------------------------------------------
-- §6 反同态：invSL (x·y) ≡ invSL y · invSL x
--
--   （x·y)·(y⁻¹·x⁻¹) = x·(y·y⁻¹)·x⁻¹ = x·x⁻¹ = e，再由 inv-unique。
--------------------------------------------------------------------------------

invSL-antihom : ∀ (x y : SL23) → invSL (x ⊗ y) ≡ invSL y ⊗ invSL x
invSL-antihom x y = sym (inv-unique (x ⊗ y) (invSL y ⊗ invSL x) (begin
    (x ⊗ y) ⊗ (invSL y ⊗ invSL x)
  ≡⟨ ⊗-assocSL x y (invSL y ⊗ invSL x) ⟩
    x ⊗ (y ⊗ (invSL y ⊗ invSL x))
  ≡⟨ cong (λ t → x ⊗ t) (sym (⊗-assocSL y (invSL y) (invSL x))) ⟩
    x ⊗ ((y ⊗ invSL y) ⊗ invSL x)
  ≡⟨ cong (λ t → x ⊗ (t ⊗ invSL x)) (invSL-right y) ⟩
    x ⊗ (g6 ⊗ invSL x)
  ≡⟨ cong (λ t → x ⊗ t) (⊗-idˡ (invSL x)) ⟩
    x ⊗ invSL x
  ≡⟨ invSL-right x ⟩
    g6
  ∎))

--------------------------------------------------------------------------------
-- §7 打包：SL23 的完整群结构
--------------------------------------------------------------------------------

record SL23GroupStructure : Set₁ where
  field
    carrier    : Set
    _·_        : carrier → carrier → carrier
    e          : carrier
    inv        : carrier → carrier
    assoc      : ∀ x y z → (x · y) · z ≡ x · (y · z)
    id-l       : ∀ x → e · x ≡ x
    id-r       : ∀ x → x · e ≡ x
    inv-l      : ∀ x → inv x · x ≡ e
    inv-r      : ∀ x → x · inv x ≡ e
    cancel-l   : ∀ x y z → x · y ≡ x · z → y ≡ z
    inv-unique-l : ∀ x y → x · y ≡ e → y ≡ inv x
    anti-hom   : ∀ x y → inv (x · y) ≡ inv y · inv x

sl23Group : SL23GroupStructure
SL23GroupStructure.carrier       sl23Group = SL23
SL23GroupStructure._·_           sl23Group = _⊗_
SL23GroupStructure.e             sl23Group = g6
SL23GroupStructure.inv           sl23Group = invSL
SL23GroupStructure.assoc         sl23Group = ⊗-assocSL
SL23GroupStructure.id-l          sl23Group = ⊗-idˡ
SL23GroupStructure.id-r          sl23Group = ⊗-idʳ
SL23GroupStructure.inv-l         sl23Group = invSL-left
SL23GroupStructure.inv-r         sl23Group = invSL-right
SL23GroupStructure.cancel-l      sl23Group = ⊗-cancelˡ
SL23GroupStructure.inv-unique-l  sl23Group = inv-unique
SL23GroupStructure.anti-hom      sl23Group = invSL-antihom
