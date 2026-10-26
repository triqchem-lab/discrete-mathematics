{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Representation.Matrix2DetMul
-- **把已证的 det-mul 从 Trit 搬到 Fin 3**（不重证）。
--
-- 为什么不重证：
--   `Algebra/Jacobian/Matrix.agda` 已有 2×2 的完整理论——
--     `det2` / `mat-mul` / `adjugate` / `det-mul-core`（8 变元版，把历史上的
--     6561 条 with/refl 收成一行）/ `det-mul` / `invertible` / `det≠0→invertible`。
--   那是 **Trit** 上的嵌套对表示；本模块只需把它沿双射搬到 **Fin 3** 的记录表示。
--
-- 桥梁（四个引理）：
--   toT        : Mat2(Fin 3) → Mat2_Trit（逐分量 fin3ToTrit）
--   det3-toT   : fin3ToTrit (det3 M) ≡ det2 (toT M)
--   mul-toT    : toT (M·N) ≡ mat-mul (toT M) (toT N)
--   det-mul3   : det3 (M·N) ≡ mul3 (det3 M) (det3 N)   ← 主定理（经 f2t-inj）
--
-- 策略：代数链（≤4 步）+ 复用 Trit 侧已证 det-mul
-- 0 postulate / 0 hole。

module Sovereign.Synthesis.Representation.Matrix2DetMul where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using
  ( Trit; T₀; _⊕_; _⊗_; negate; fin3ToTrit; tritToFin3 )
open import Sovereign.Algebra.FieldTower.GF27 using (negate-⊗)
open import Sovereign.Algebra.Jacobian.Discrete using ()
  renaming ( Mat2 to Mat2T; det2 to det2T )
open import Sovereign.Algebra.Jacobian.Matrix using (mat-mul; det-mul)

open import Sovereign.Synthesis.Representation.Fin3Semiring using
  ( f2t-inj; f2t-add; f2t-mul; neg3 )
-- ⚠ add3/mul3 不是 Fin3Semiring 的自有定义（它只导入），故直接从源头取
open import Sovereign.Synthesis.Representation.SL23Cayley using (add3; mul3; Mat2; mulMat2)
open import Sovereign.Synthesis.Representation.Matrix2Inverse using (det3)
open import Sovereign.Algebra.LinearAlgebra.Matrix2 using (mkMat2; m00; m01; m10; m11)

--------------------------------------------------------------------------------
-- 1. 矩阵的搬运（Fin 3 记录 → Trit 嵌套对）
--------------------------------------------------------------------------------

toT : Mat2 → Mat2T
toT (mkMat2 a b c d) =
  (fin3ToTrit a , fin3ToTrit b) , (fin3ToTrit c , fin3ToTrit d)

-- 取反在搬运下对应（3 case）
f2t-neg3 : ∀ x → fin3ToTrit (neg3 x) ≡ Sovereign.Base.Trit.negate (fin3ToTrit x)
f2t-neg3 zero             = refl
f2t-neg3 (suc zero)       = refl
f2t-neg3 (suc (suc zero)) = refl

--------------------------------------------------------------------------------
-- 2. 行列式与乘法在搬运下的相容
--------------------------------------------------------------------------------

det3-toT : ∀ M → fin3ToTrit (det3 M) ≡ det2T (toT M)
det3-toT (mkMat2 a b c d) =
  trans (f2t-add (mul3 a d) (mul3 (neg3 b) c))                       -- 加法拆开
    (cong₂ (λ u v → u Sovereign.Base.Trit.⊕ v)
           (f2t-mul a d)                                              -- a·d
           (trans (f2t-mul (neg3 b) c)                                -- (−b)·c
             (trans (cong (λ u → u Sovereign.Base.Trit.⊗ fin3ToTrit c) (f2t-neg3 b))
                    (sym (negate-⊗ (fin3ToTrit b) (fin3ToTrit c))))))  -- (−b)⊗c → −(b⊗c)

mul-toT : ∀ M N → toT (mulMat2 M N) ≡ mat-mul (toT M) (toT N)
mul-toT (mkMat2 a b c d) (mkMat2 e f g h) =
  cong₂ _,_
    (cong₂ _,_
      (trans (f2t-add (mul3 a e) (mul3 b g))
             (cong₂ Sovereign.Base.Trit._⊕_ (f2t-mul a e) (f2t-mul b g)))
      (trans (f2t-add (mul3 a f) (mul3 b h))
             (cong₂ Sovereign.Base.Trit._⊕_ (f2t-mul a f) (f2t-mul b h))))
    (cong₂ _,_
      (trans (f2t-add (mul3 c e) (mul3 d g))
             (cong₂ Sovereign.Base.Trit._⊕_ (f2t-mul c e) (f2t-mul d g)))
      (trans (f2t-add (mul3 c f) (mul3 d h))
             (cong₂ Sovereign.Base.Trit._⊕_ (f2t-mul c f) (f2t-mul d h))))

--------------------------------------------------------------------------------
-- 3. 主定理：det 的乘法性（Fin 3 版，取自 Trit 侧已证的 det-mul）
--------------------------------------------------------------------------------

det-mul3 : ∀ M N → det3 (mulMat2 M N) ≡ mul3 (det3 M) (det3 N)
det-mul3 M N =
  f2t-inj
    (trans (det3-toT (mulMat2 M N))                                    -- f2t·det3(MN) = det2(toT(MN))
      (trans (cong det2T (mul-toT M N))                                -- toT(MN) = toT M · toT N
        (trans (det-mul (toT M) (toT N))                              -- det2(MN) = det2 M ⊗ det2 N
          (trans (cong₂ (λ u v → u Sovereign.Base.Trit.⊗ v)
                        (sym (det3-toT M)) (sym (det3-toT N)))         -- 落回 f2t·det3
                 (sym (f2t-mul (det3 M) (det3 N)))))))                 -- f2t(mul3 …)
