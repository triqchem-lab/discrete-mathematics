{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Representation.Fin3Semiring
-- **Fin 3 的交换半环结构与 2×2 矩阵幺半群律**（GF(3) 运算的公共底座）。
--
-- 为什么需要这一件：
--   · `Mat2 = Matrix2F (Fin 3)`（SL23Cayley），系数是 **Fin 3**；
--   · 而 `Base/Trit.agda` 的 14 条环律建在 **Trit** 这个独立归纳类型上；
--   · Trit 与 Fin 3 同基数、有互逆双射（`tritToFin3` / `fin3ToTrit`），
--     故把环律经双射搬到 Fin 3，得到 `CommSemiring (Fin 3)`，避免重做
--     ~144 条 case 穷举。
--
-- 包含：双射注入性 f2t-inj / 兼容引理 f2t-add,f2t-mul / 14 条环律 /
--       fin3CS / I2 / 矩阵幺半群三律 / neg3 与四条取反引理
--
-- 策略：代数链（每条律 1–5 步，底板是 Trit 已证的穷举律）｜来源：Matrix2Laws 泛型矩阵律
-- 0 postulate / 0 hole。

module Sovereign.Synthesis.Representation.Fin3Semiring where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using
  ( Trit; T₀; T₁; T₂; _⊕_; _⊗_
  ; tritToFin3; fin3ToTrit; tr-to-f3-to-tr; f3-to-tr-to-f3
  ; ⊕-assoc; ⊕-comm; ⊕-identityˡ; ⊕-identityʳ
  ; ⊗-assoc; ⊗-comm; ⊗-identityˡ; ⊗-identityʳ
  ; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-zeroˡ; ⊗-zeroʳ )
open import Sovereign.Algebra.UniversalAlgebra.UniversalAlgebra using (CommSemiring)
open import Sovereign.Algebra.LinearAlgebra.Matrix2 using (mkMat2)

-- Mat2 取 SL23Cayley 的**实例**（= Matrix2F (Fin 3)）；mulMat2 是已绑定 add3/mul3 的二元版
open import Sovereign.Synthesis.Representation.SL23Cayley using (Mat2; mulMat2; add3; mul3)

--------------------------------------------------------------------------------
-- 1. 双射注入性与兼容引理
--------------------------------------------------------------------------------

f2t-inj : ∀ {x y : Fin 3} → fin3ToTrit x ≡ fin3ToTrit y → x ≡ y
f2t-inj {x} {y} eq =
  trans (sym (f3-to-tr-to-f3 x)) (trans (cong tritToFin3 eq) (f3-to-tr-to-f3 y))

-- add3/mul3 与 ⊕/⊗ 相容（各 9 case refl）
f2t-add : ∀ x y → fin3ToTrit (add3 x y) ≡ fin3ToTrit x ⊕ fin3ToTrit y
f2t-add zero y                            = refl
f2t-add (suc zero) zero                   = refl
f2t-add (suc zero) (suc zero)             = refl
f2t-add (suc zero) (suc (suc zero))       = refl
f2t-add (suc (suc zero)) zero             = refl
f2t-add (suc (suc zero)) (suc zero)       = refl
f2t-add (suc (suc zero)) (suc (suc zero)) = refl

f2t-mul : ∀ x y → fin3ToTrit (mul3 x y) ≡ fin3ToTrit x ⊗ fin3ToTrit y
f2t-mul zero y                            = refl
-- ⚠ T₁ ⊗ z 对中性 z 不归约（`_ ⊗ T₀` 子句使判定树先分裂第二元）⇒ 用 ⊗-identityˡ
f2t-mul (suc zero) y                      = sym (⊗-identityˡ (fin3ToTrit y))
f2t-mul (suc (suc zero)) zero             = refl
f2t-mul (suc (suc zero)) (suc zero)       = refl
f2t-mul (suc (suc zero)) (suc (suc zero)) = refl

--------------------------------------------------------------------------------
-- 2. 十四条环律（每条：抬到 Trit → 用已证的 Trit 律 → 落回 Fin 3）
--------------------------------------------------------------------------------

add3-assoc : ∀ x y z → add3 (add3 x y) z ≡ add3 x (add3 y z)
add3-assoc x y z =
  f2t-inj (trans (f2t-add (add3 x y) z)
    (trans (cong (λ u → u ⊕ fin3ToTrit z) (f2t-add x y))
      (trans (⊕-assoc (fin3ToTrit x) (fin3ToTrit y) (fin3ToTrit z))
        (trans (cong (fin3ToTrit x ⊕_) (sym (f2t-add y z)))
               (sym (f2t-add x (add3 y z)))))))

add3-comm : ∀ x y → add3 x y ≡ add3 y x
add3-comm x y =
  f2t-inj (trans (f2t-add x y)
            (trans (⊕-comm (fin3ToTrit x) (fin3ToTrit y)) (sym (f2t-add y x))))

add3-idˡ : ∀ x → add3 zero x ≡ x
add3-idˡ zero             = refl
add3-idˡ (suc zero)       = refl
add3-idˡ (suc (suc zero)) = refl

add3-idʳ : ∀ x → add3 x zero ≡ x
add3-idʳ zero             = refl
add3-idʳ (suc zero)       = refl
add3-idʳ (suc (suc zero)) = refl

mul3-assoc : ∀ x y z → mul3 (mul3 x y) z ≡ mul3 x (mul3 y z)
mul3-assoc x y z =
  f2t-inj (trans (f2t-mul (mul3 x y) z)
    (trans (cong (λ u → u ⊗ fin3ToTrit z) (f2t-mul x y))
      (trans (⊗-assoc (fin3ToTrit x) (fin3ToTrit y) (fin3ToTrit z))
        (trans (cong (fin3ToTrit x ⊗_) (sym (f2t-mul y z)))
               (sym (f2t-mul x (mul3 y z)))))))

mul3-comm : ∀ x y → mul3 x y ≡ mul3 y x
mul3-comm x y =
  f2t-inj (trans (f2t-mul x y)
            (trans (⊗-comm (fin3ToTrit x) (fin3ToTrit y)) (sym (f2t-mul y x))))

mul3-idˡ : ∀ x → mul3 (suc zero) x ≡ x
mul3-idˡ zero             = refl
mul3-idˡ (suc zero)       = refl
mul3-idˡ (suc (suc zero)) = refl

mul3-idʳ : ∀ x → mul3 x (suc zero) ≡ x
mul3-idʳ zero             = refl
mul3-idʳ (suc zero)       = refl
mul3-idʳ (suc (suc zero)) = refl

mul3-zeroˡ : ∀ x → mul3 zero x ≡ zero
mul3-zeroˡ zero             = refl
mul3-zeroˡ (suc zero)       = refl
mul3-zeroˡ (suc (suc zero)) = refl

mul3-zeroʳ : ∀ x → mul3 x zero ≡ zero
mul3-zeroʳ zero             = refl
mul3-zeroʳ (suc zero)       = refl
mul3-zeroʳ (suc (suc zero)) = refl

mul3-distribˡ : ∀ x y z → mul3 x (add3 y z) ≡ add3 (mul3 x y) (mul3 x z)
mul3-distribˡ x y z =
  f2t-inj (trans (f2t-mul x (add3 y z))
    (trans (cong (fin3ToTrit x ⊗_) (f2t-add y z))
      (trans (⊗-distribˡ-⊕ (fin3ToTrit x) (fin3ToTrit y) (fin3ToTrit z))
        (trans (cong₂ _⊕_ (sym (f2t-mul x y)) (sym (f2t-mul x z)))
               (sym (f2t-add (mul3 x y) (mul3 x z)))))))

mul3-distribʳ : ∀ x y z → mul3 (add3 y z) x ≡ add3 (mul3 y x) (mul3 z x)
mul3-distribʳ x y z =
  f2t-inj (trans (f2t-mul (add3 y z) x)
    (trans (cong (λ u → u ⊗ fin3ToTrit x) (f2t-add y z))
      (trans (⊗-distribʳ-⊕ (fin3ToTrit y) (fin3ToTrit z) (fin3ToTrit x))
        (trans (cong₂ _⊕_ (sym (f2t-mul y x)) (sym (f2t-mul z x)))
               (sym (f2t-add (mul3 y x) (mul3 z x)))))))

fin3CS : CommSemiring (Fin 3)
fin3CS = record
  { _+_      = add3
  ; _*_      = mul3
  ; zero     = zero
  ; one      = suc zero
  ; +-assoc  = add3-assoc
  ; +-comm   = add3-comm
  ; +-idˡ    = add3-idˡ
  ; +-idʳ    = add3-idʳ
  ; *-assoc  = mul3-assoc
  ; *-comm   = mul3-comm
  ; *-idˡ    = mul3-idˡ
  ; *-idʳ    = mul3-idʳ
  ; distribˡ = mul3-distribˡ
  ; distribʳ = mul3-distribʳ
  ; zeroˡ    = mul3-zeroˡ
  ; zeroʳ    = mul3-zeroʳ
  }

--------------------------------------------------------------------------------
-- 3. GF(3) 上 2×2 矩阵的幺半群律（实例化 Matrix2Laws 的泛型件）
--------------------------------------------------------------------------------

open import Sovereign.Algebra.LinearAlgebra.Matrix2Laws using
  ( mulMat2-assoc; mulMat2-idˡ; mulMat2-idʳ )

I2 : Mat2
I2 = mkMat2 (suc zero) zero zero (suc zero)

mat-assoc : ∀ X Y Z → mulMat2 (mulMat2 X Y) Z ≡ mulMat2 X (mulMat2 Y Z)
mat-assoc = mulMat2-assoc fin3CS

mat-idˡ : ∀ X → mulMat2 I2 X ≡ X
mat-idˡ = mulMat2-idˡ fin3CS

mat-idʳ : ∀ X → mulMat2 X I2 ≡ X
mat-idʳ = mulMat2-idʳ fin3CS

--------------------------------------------------------------------------------
-- 4. 取反（GF(3) 里 −x = 2x = x + x）
--------------------------------------------------------------------------------

neg3 : Fin 3 → Fin 3
neg3 zero             = zero
neg3 (suc zero)       = suc (suc zero)
neg3 (suc (suc zero)) = suc zero

neg3-zero : neg3 zero ≡ zero
neg3-zero = refl

-- x + (−x) = 0（3 case）
neg3-inv : ∀ x → add3 x (neg3 x) ≡ zero
neg3-inv zero             = refl
neg3-inv (suc zero)       = refl
neg3-inv (suc (suc zero)) = refl

-- −(x+y) = (−x)+(−y)（9 case）
neg3-add : ∀ x y → neg3 (add3 x y) ≡ add3 (neg3 x) (neg3 y)
neg3-add zero y                            = refl
neg3-add (suc zero) zero                   = refl
neg3-add (suc zero) (suc zero)             = refl
neg3-add (suc zero) (suc (suc zero))       = refl
neg3-add (suc (suc zero)) zero             = refl
neg3-add (suc (suc zero)) (suc zero)       = refl
neg3-add (suc (suc zero)) (suc (suc zero)) = refl

-- 取反对合：−(−x) = x（3 case）—— det(adj M) = det M 需要
neg3-invol : ∀ x → neg3 (neg3 x) ≡ x
neg3-invol zero             = refl
neg3-invol (suc zero)       = refl
neg3-invol (suc (suc zero)) = refl

-- (−x)·y = −(x·y)（9 case）
neg3-mulˡ : ∀ x y → mul3 (neg3 x) y ≡ neg3 (mul3 x y)
neg3-mulˡ zero y                            = refl
neg3-mulˡ (suc zero) zero                   = refl
neg3-mulˡ (suc zero) (suc zero)             = refl
neg3-mulˡ (suc zero) (suc (suc zero))       = refl
neg3-mulˡ (suc (suc zero)) zero             = refl
neg3-mulˡ (suc (suc zero)) (suc zero)       = refl
neg3-mulˡ (suc (suc zero)) (suc (suc zero)) = refl

-- x·(−y) = −(x·y)（9 case）
neg3-mulʳ : ∀ x y → mul3 x (neg3 y) ≡ neg3 (mul3 x y)
neg3-mulʳ x y = trans (mul3-comm x (neg3 y)) (trans (neg3-mulˡ y x) (cong neg3 (mul3-comm y x)))
