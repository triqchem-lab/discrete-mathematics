{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.Matrix2Laws
-- 2×2 矩阵乘法的**幺半群律**（结合律 + 双边单位律），在任意交换半环上成立。
--
-- 为什么单独一件：
--   · `Matrix2.agda` 只给运算（84 行），**无任何律**；
--   · `SL23Cayley` 证的是 576 对**封闭性**（toMat(x⊗y) ≡ mulMat2 (toMat x) (toMat y)），
--     不是结合律；
--   · `A4ThreeDimRep.agda:329` 自述「需 mulMat-assoc 把右嵌套链重排, 其分量证明逐条消耗」
--     —— 即需求早已登记，件一直缺。
--   · 下游要它：BraidToSL23 的「eval 是同态」、GroupData Mat2 的实例、
--     BraidGroup 里左右括号两种词的等价。
--
-- 策略：**一次证泛型版**（对 CommSemiring 抽象），再在 Trit 上实例化——
--   而不是对 Fin 3 做 3¹² 穷举。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.LinearAlgebra.Matrix2Laws where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Sovereign.Algebra.UniversalAlgebra.UniversalAlgebra using (CommSemiring)
open import Sovereign.Algebra.LinearAlgebra.Matrix2 using
  ( Mat2; mkMat2; mulMat2; m00; m01; m10; m11 )

module _ {A : Set} (R : CommSemiring A) where

  open CommSemiring R

  ------------------------------------------------------------------------------
  -- 1. 四元换位：加法的二维重排单元（同 GF9.agda 的 swap-middle）
  ------------------------------------------------------------------------------

  swap-middle : ∀ w x y z → (w + x) + (y + z) ≡ (w + y) + (x + z)
  swap-middle w x y z =
    trans (sym (+-assoc (w + x) y z))
      (trans (cong (λ t → t + z) (+-assoc w x y))
        (trans (cong (λ t → (w + t) + z) (+-comm x y))
          (trans (cong (λ t → t + z) (sym (+-assoc w y x)))
                 (+-assoc (w + y) x z))))

  ------------------------------------------------------------------------------
  -- 2. 单个分量的结合律（2×2 的四个分量都归约到同一个 8 变元形状）
  ------------------------------------------------------------------------------

  -- 对应 ((A·B)·C)₀₀ 与 (A·(B·C))₀₀ 的形状：
  --   (((p*q) + (r*s)) * t) + (((p*u) + (r*v)) * w)
  --   ≡ (p * ((q*t) + (u*w))) + (r * ((s*t) + (v*w)))
  key : ∀ p q r s t u v w →
        (((p * q) + (r * s)) * t) + (((p * u) + (r * v)) * w)
      ≡ (p * ((q * t) + (u * w))) + (r * ((s * t) + (v * w)))
  key p q r s t u v w =
    trans step1
      (trans (swap-middle (p * (q * t)) (r * (s * t))
                          (p * (u * w)) (r * (v * w)))
             step2)
    where
      step1 : (((p * q) + (r * s)) * t) + (((p * u) + (r * v)) * w)
            ≡ (p * (q * t) + r * (s * t)) + (p * (u * w) + r * (v * w))
      step1 =
        trans (cong₂ _+_ (distribʳ t (p * q) (r * s))
                         (distribʳ w (p * u) (r * v)))
              (cong₂ _+_
                (cong₂ _+_ (*-assoc p q t) (*-assoc r s t))
                (cong₂ _+_ (*-assoc p u w) (*-assoc r v w)))

      step2 : (p * (q * t) + p * (u * w)) + (r * (s * t) + r * (v * w))
            ≡ (p * ((q * t) + (u * w))) + (r * ((s * t) + (v * w)))
      step2 = cong₂ _+_ (sym (distribˡ p (q * t) (u * w)))
                        (sym (distribˡ r (s * t) (v * w)))

  ------------------------------------------------------------------------------
  -- 3. 记录相等从分量相等装配
  ------------------------------------------------------------------------------

  mat2-cong : ∀ {a a' b b' c c' d d' : A}
            → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d'
            → mkMat2 a b c d ≡ mkMat2 a' b' c' d'
  mat2-cong {a} {a'} {b} {b'} {c} {c'} {d} {d'} p q r s =
    trans (cong (λ x → mkMat2 x b c d) p)
      (trans (cong (λ y → mkMat2 a' y c d) q)
        (trans (cong (λ z → mkMat2 a' b' z d) r)
               (cong (λ w → mkMat2 a' b' c' w) s)))

  ------------------------------------------------------------------------------
  -- 4. 结合律（泛型）
  ------------------------------------------------------------------------------

  mulMat2-assoc : ∀ (X Y Z : Mat2 A)
                → mulMat2 _+_ _*_ (mulMat2 _+_ _*_ X Y) Z
                ≡ mulMat2 _+_ _*_ X (mulMat2 _+_ _*_ Y Z)
  mulMat2-assoc (mkMat2 a b c d) (mkMat2 e f g h) (mkMat2 i j k l) =
    mat2-cong
      (key a e b g i f h k)      -- 分量 00
      (key a e b g j f h l)      -- 分量 01
      (key c e d g i f h k)      -- 分量 10
      (key c e d g j f h l)      -- 分量 11

  ------------------------------------------------------------------------------
  -- 5. 双边单位律（泛型）
  ------------------------------------------------------------------------------

  -- one*a + zero*c ≡ a
  entry-idˡ-a : ∀ a c → (one * a) + (zero * c) ≡ a
  entry-idˡ-a a c = trans (cong₂ _+_ (*-idˡ a) (zeroˡ c)) (+-idʳ a)

  -- a*one + c*zero ≡ a
  entry-idʳ-a : ∀ a c → (a * one) + (c * zero) ≡ a
  entry-idʳ-a a c = trans (cong₂ _+_ (*-idʳ a) (zeroʳ c)) (+-idʳ a)

  mulMat2-idˡ : ∀ (X : Mat2 A) → mulMat2 _+_ _*_ (mkMat2 one zero zero one) X ≡ X
  mulMat2-idˡ (mkMat2 a b c d) =
    mat2-cong
      (entry-idˡ-a a c)
      (entry-idˡ-a b d)
      (trans (cong₂ _+_ (zeroˡ a) (*-idˡ c)) (+-idˡ c))
      (trans (cong₂ _+_ (zeroˡ b) (*-idˡ d)) (+-idˡ d))

  mulMat2-idʳ : ∀ (X : Mat2 A) → mulMat2 _+_ _*_ X (mkMat2 one zero zero one) ≡ X
  mulMat2-idʳ (mkMat2 a b c d) =
    mat2-cong
      (entry-idʳ-a a b)
      (trans (cong₂ _+_ (zeroʳ a) (*-idʳ b)) (+-idˡ b))
      (entry-idʳ-a c d)
      (trans (cong₂ _+_ (zeroʳ c) (*-idʳ d)) (+-idˡ d))

--------------------------------------------------------------------------------
-- 6. GF(3) 实例：Trit 上的环律已在 Base/Trit 全部证毕，直接组装
--

open import Sovereign.Base.Trit using
  ( Trit; T₀; T₁; _⊕_; _⊗_
  ; ⊕-assoc; ⊕-comm; ⊕-identityˡ; ⊕-identityʳ
  ; ⊗-assoc; ⊗-comm; ⊗-identityˡ; ⊗-identityʳ
  ; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-zeroˡ; ⊗-zeroʳ )

tritCS : CommSemiring Trit
tritCS = record
  { _+_       = _⊕_
  ; _*_       = _⊗_
  ; zero      = T₀
  ; one       = T₁
  ; +-assoc   = ⊕-assoc
  ; +-comm    = ⊕-comm
  ; +-idˡ     = ⊕-identityˡ
  ; +-idʳ     = ⊕-identityʳ
  ; *-assoc   = ⊗-assoc
  ; *-comm    = ⊗-comm
  ; *-idˡ     = ⊗-identityˡ
  ; *-idʳ     = ⊗-identityʳ
  ; distribˡ  = ⊗-distribˡ-⊕
  ; distribʳ  = λ a b c → ⊗-distribʳ-⊕ b c a
  ; zeroˡ     = ⊗-zeroˡ
  ; zeroʳ     = ⊗-zeroʳ
  }

-- GF(3) 上 2×2 矩阵乘法的三条律（用 _⊕_/_⊗_ 直接表述）
mat-assoc-3 : ∀ (X Y Z : Mat2 Trit)
            → mulMat2 _⊕_ _⊗_ (mulMat2 _⊕_ _⊗_ X Y) Z
            ≡ mulMat2 _⊕_ _⊗_ X (mulMat2 _⊕_ _⊗_ Y Z)
mat-assoc-3 = mulMat2-assoc tritCS

mat-idˡ-3 : ∀ (X : Mat2 Trit)
          → mulMat2 _⊕_ _⊗_ (mkMat2 T₁ T₀ T₀ T₁) X ≡ X
mat-idˡ-3 = mulMat2-idˡ tritCS

mat-idʳ-3 : ∀ (X : Mat2 Trit)
          → mulMat2 _⊕_ _⊗_ X (mkMat2 T₁ T₀ T₀ T₁) ≡ X
mat-idʳ-3 = mulMat2-idʳ tritCS
