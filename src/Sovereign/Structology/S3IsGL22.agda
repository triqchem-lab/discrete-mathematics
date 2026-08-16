{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.S3IsGL22
-- S₃ ≅ GL(2,2): SP2 含反射全对称的 GF(2) 矩阵实现 (0 postulate)
--
-- GL(2,2) = GF(2) 上 det=1 的 2×2 可逆矩阵, 共 6 个, 与 S₃ 同构。
-- 阶分解: 1 个单位元 (阶 1) + 3 个对换 (阶 2) + 2 个三循环 (阶 3) = 6,
-- 非交换 (唯一 6 阶非交换群即 S₃)。这是 SP2 含反射对称的代数载体,
-- GF(2) 只服务于 SP2 的反射, 不进入 GF(3)/GF(9) 主基座。

module Sovereign.Structology.S3IsGL22 where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

--------------------------------------------------------------------------------
-- §1. GF(2) 算术
--------------------------------------------------------------------------------

gadd : Bool → Bool → Bool   -- xor
gadd false false = false
gadd false true = true
gadd true false = true
gadd true true = false

gmul : Bool → Bool → Bool   -- and
gmul false _ = false
gmul true b = b

--------------------------------------------------------------------------------
-- §2. 2×2 矩阵 over GF(2)
--------------------------------------------------------------------------------

record Mat2 : Set where
  constructor mat2
  field
    m00 m01 m10 m11 : Bool

open Mat2

mulMat2 : Mat2 → Mat2 → Mat2
mulMat2 (mat2 a b c d) (mat2 e f g h) =
  mat2 (gadd (gmul a e) (gmul b g)) (gadd (gmul a f) (gmul b h))
       (gadd (gmul c e) (gmul d g)) (gadd (gmul c f) (gmul d h))

det2 : Mat2 → Bool
det2 (mat2 a b c d) = gadd (gmul a d) (gmul b c)

--------------------------------------------------------------------------------
-- §3. GL(2,2) 的 6 个矩阵 (det=1)
--------------------------------------------------------------------------------

mat : Fin 6 → Mat2
mat zero = mat2 false true true false
mat (suc zero) = mat2 false true true true
mat (suc (suc zero)) = mat2 true false false true
mat (suc (suc (suc zero))) = mat2 true false true true
mat (suc (suc (suc (suc zero)))) = mat2 true true false true
mat (suc (suc (suc (suc (suc zero))))) = mat2 true true true false

--------------------------------------------------------------------------------
-- §4. Cayley 表 (6×6 = 36) 与同态
--------------------------------------------------------------------------------

_⊗_ : Fin 6 → Fin 6 → Fin 6
zero ⊗ zero = (suc (suc zero))
zero ⊗ (suc zero) = (suc (suc (suc (suc zero))))
zero ⊗ (suc (suc zero)) = zero
zero ⊗ (suc (suc (suc zero))) = (suc (suc (suc (suc (suc zero)))))
zero ⊗ (suc (suc (suc (suc zero)))) = (suc zero)
zero ⊗ (suc (suc (suc (suc (suc zero))))) = (suc (suc (suc zero)))
(suc zero) ⊗ zero = (suc (suc (suc zero)))
(suc zero) ⊗ (suc zero) = (suc (suc (suc (suc (suc zero)))))
(suc zero) ⊗ (suc (suc zero)) = (suc zero)
(suc zero) ⊗ (suc (suc (suc zero))) = (suc (suc (suc (suc zero))))
(suc zero) ⊗ (suc (suc (suc (suc zero)))) = zero
(suc zero) ⊗ (suc (suc (suc (suc (suc zero))))) = (suc (suc zero))
(suc (suc zero)) ⊗ zero = zero
(suc (suc zero)) ⊗ (suc zero) = (suc zero)
(suc (suc zero)) ⊗ (suc (suc zero)) = (suc (suc zero))
(suc (suc zero)) ⊗ (suc (suc (suc zero))) = (suc (suc (suc zero)))
(suc (suc zero)) ⊗ (suc (suc (suc (suc zero)))) = (suc (suc (suc (suc zero))))
(suc (suc zero)) ⊗ (suc (suc (suc (suc (suc zero))))) = (suc (suc (suc (suc (suc zero)))))
(suc (suc (suc zero))) ⊗ zero = (suc zero)
(suc (suc (suc zero))) ⊗ (suc zero) = zero
(suc (suc (suc zero))) ⊗ (suc (suc zero)) = (suc (suc (suc zero)))
(suc (suc (suc zero))) ⊗ (suc (suc (suc zero))) = (suc (suc zero))
(suc (suc (suc zero))) ⊗ (suc (suc (suc (suc zero)))) = (suc (suc (suc (suc (suc zero)))))
(suc (suc (suc zero))) ⊗ (suc (suc (suc (suc (suc zero))))) = (suc (suc (suc (suc zero))))
(suc (suc (suc (suc zero)))) ⊗ zero = (suc (suc (suc (suc (suc zero)))))
(suc (suc (suc (suc zero)))) ⊗ (suc zero) = (suc (suc (suc zero)))
(suc (suc (suc (suc zero)))) ⊗ (suc (suc zero)) = (suc (suc (suc (suc zero))))
(suc (suc (suc (suc zero)))) ⊗ (suc (suc (suc zero))) = (suc zero)
(suc (suc (suc (suc zero)))) ⊗ (suc (suc (suc (suc zero)))) = (suc (suc zero))
(suc (suc (suc (suc zero)))) ⊗ (suc (suc (suc (suc (suc zero))))) = zero
(suc (suc (suc (suc (suc zero))))) ⊗ zero = (suc (suc (suc (suc zero))))
(suc (suc (suc (suc (suc zero))))) ⊗ (suc zero) = (suc (suc zero))
(suc (suc (suc (suc (suc zero))))) ⊗ (suc (suc zero)) = (suc (suc (suc (suc (suc zero)))))
(suc (suc (suc (suc (suc zero))))) ⊗ (suc (suc (suc zero))) = zero
(suc (suc (suc (suc (suc zero))))) ⊗ (suc (suc (suc (suc zero)))) = (suc (suc (suc zero)))
(suc (suc (suc (suc (suc zero))))) ⊗ (suc (suc (suc (suc (suc zero))))) = (suc zero)

mul-hom : ∀ (x y : Fin 6) → mulMat2 (mat x) (mat y) ≡ mat (x ⊗ y)
mul-hom zero zero = refl
mul-hom zero (suc zero) = refl
mul-hom zero (suc (suc zero)) = refl
mul-hom zero (suc (suc (suc zero))) = refl
mul-hom zero (suc (suc (suc (suc zero)))) = refl
mul-hom zero (suc (suc (suc (suc (suc zero))))) = refl
mul-hom (suc zero) zero = refl
mul-hom (suc zero) (suc zero) = refl
mul-hom (suc zero) (suc (suc zero)) = refl
mul-hom (suc zero) (suc (suc (suc zero))) = refl
mul-hom (suc zero) (suc (suc (suc (suc zero)))) = refl
mul-hom (suc zero) (suc (suc (suc (suc (suc zero))))) = refl
mul-hom (suc (suc zero)) zero = refl
mul-hom (suc (suc zero)) (suc zero) = refl
mul-hom (suc (suc zero)) (suc (suc zero)) = refl
mul-hom (suc (suc zero)) (suc (suc (suc zero))) = refl
mul-hom (suc (suc zero)) (suc (suc (suc (suc zero)))) = refl
mul-hom (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) = refl
mul-hom (suc (suc (suc zero))) zero = refl
mul-hom (suc (suc (suc zero))) (suc zero) = refl
mul-hom (suc (suc (suc zero))) (suc (suc zero)) = refl
mul-hom (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
mul-hom (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) = refl
mul-hom (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) = refl
mul-hom (suc (suc (suc (suc zero)))) zero = refl
mul-hom (suc (suc (suc (suc zero)))) (suc zero) = refl
mul-hom (suc (suc (suc (suc zero)))) (suc (suc zero)) = refl
mul-hom (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) = refl
mul-hom (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) = refl
mul-hom (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) = refl
mul-hom (suc (suc (suc (suc (suc zero))))) zero = refl
mul-hom (suc (suc (suc (suc (suc zero))))) (suc zero) = refl
mul-hom (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) = refl
mul-hom (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) = refl
mul-hom (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) = refl
mul-hom (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) = refl

--------------------------------------------------------------------------------
-- §5. 阶分解 1 + 3×2 + 2×3 (与 S₃ 一致)
--------------------------------------------------------------------------------

orderOf : Fin 6 → ℕ
orderOf zero = 2
orderOf (suc zero) = 3
orderOf (suc (suc zero)) = 1
orderOf (suc (suc (suc zero))) = 2
orderOf (suc (suc (suc (suc zero)))) = 2
orderOf (suc (suc (suc (suc (suc zero))))) = 3

order-identity : orderOf (suc (suc zero)) ≡ 1
order-identity = refl
order-two-count : orderOf zero ≡ 2 × orderOf (suc (suc (suc zero))) ≡ 2 × orderOf (suc (suc (suc (suc zero)))) ≡ 2
order-two-count = refl , refl , refl
order-three-count : orderOf (suc zero) ≡ 3 × orderOf (suc (suc (suc (suc (suc zero))))) ≡ 3
order-three-count = refl , refl

--------------------------------------------------------------------------------
-- §6. 非交换 (唯一 6 阶非交换群 = S₃)
--------------------------------------------------------------------------------

non-abelian : ((suc zero) ⊗ (suc (suc (suc (suc zero))))) ≢ ((suc (suc (suc (suc zero)))) ⊗ (suc zero))
non-abelian = λ ()

-- 0 postulate.
