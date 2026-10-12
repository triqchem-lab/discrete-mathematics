{-# OPTIONS --cubical --guardedness #-}
module Probe9 where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm)

swap3 : ∀ p q r → p + (q + r) ≡ q + (p + r)
swap3 p q r = +Assoc p q r ∙ cong (_+ r) (+Comm p q) ∙ sym (+Assoc q p r)

assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)


-- tail-p1..p6：收尾段 6 步独立引理
tail-p1 : ∀ v1 v4 (Y : ℤ) → v1 + (v4 + Y) ≡ (v1 + v4) + Y
tail-p1 v1 v4 Y = +Assoc v1 v4 Y

tail-p2 : ∀ v1 v4 v2 v7 (Z : ℤ) →
  (v1 + v4) + ((v2 + v7) + Z) ≡ (v1 + v4) + (v2 + (v7 + Z))
tail-p2 v1 v4 v2 v7 Z = cong (λ w → (v1 + v4) + w) (sym (+Assoc v2 v7 Z))

tail-p3 : ∀ v1 v4 v2 v7 (Z : ℤ) →
  (v1 + v4) + (v2 + (v7 + Z)) ≡ (v1 + v4) + (v7 + (v2 + Z))
tail-p3 v1 v4 v2 v7 Z = cong (λ w → (v1 + v4) + w) (swap3 v2 v7 Z)

tail-p4 : ∀ v1 v4 v7 v2 (Z : ℤ) →
  (v1 + v4) + (v7 + (v2 + Z)) ≡ ((v1 + v4) + v7) + (v2 + Z)
tail-p4 v1 v4 v7 v2 Z = +Assoc (v1 + v4) v7 (v2 + Z)

tail-c1 : ∀ v1 v4 v7 v2 v5 (Z : ℤ) →
  ((v1 + v4) + v7) + (v2 + (v5 + Z)) ≡ ((v1 + v4) + v7) + ((v2 + v5) + Z)
tail-c1 v1 v4 v7 v2 v5 Z = cong (λ w → ((v1 + v4) + v7) + w) (+Assoc v2 v5 Z)


tail-p7 : ∀ (v1 v4 v7 v2 v5 v8 v3 v6 v9 : ℤ) →
  ((v1 + v4) + v7) + ((v2 + v5) + (v8 + ((v3 + v6) + v9)))
  ≡ ((v1 + v4) + v7) + (((v2 + v5) + v8) + ((v3 + v6) + v9))
tail-p7 v1 v4 v7 v2 v5 v8 v3 v6 v9 =
      +Assoc (v2 + v5) v8 ((v3 + v6) + v9)

tail-c2 : ∀ (v1 v4 v7 v2 v5 v8 v3 v6 v9 : ℤ) →
  ((v1 + v4) + v7) + ((v2 + v5) + (v8 + (v3 + (v6 + v9))))
  ≡ ((v1 + v4) + v7) + ((v2 + v5) + ((v8 + (v3 + v6)) + v9))
tail-c2 v1 v4 v7 v2 v5 v8 v3 v6 v9 =
  let m1 : v3 + (v6 + v9) ≡ (v3 + v6) + v9
      m1 = assocP v3 v6 v9
      X1 = ((v1 + v4) + v7) + ((v2 + v5) + (v8 + (v3 + (v6 + v9))))
      X2 = ((v1 + v4) + v7) + ((v2 + v5) + (v8 + ((v3 + v6) + v9)))
      p1 : X1 ≡ X2
      p1 = cong (λ w → ((v1 + v4) + v7) + ((v2 + v5) + (v8 + w))) m1
      p2 : X2 ≡ ((v1 + v4) + v7) + ((v2 + v5) + ((v8 + (v3 + v6)) + v9))
      p2 = tail-p7 v1 v4 v7 v2 v5 v8 v3 v6 v9
  in p1 ∙ p2
tail-c3 : ∀ (v1 v4 v7 v2 v5 v8 v3 v6 v9 : ℤ) →
  ((v1 + v4) + v7) + ((v2 + v5) + (v8 + ((v3 + v6) + v9)))
  ≡ (((v1 + v4) + v7) + ((v2 + v5) + v8)) + ((v3 + v6) + v9)
tail-c3 v1 v4 v7 v2 v5 v8 v3 v6 v9 =
  cong (λ w → ((v1 + v4) + v7) + w) (+Assoc (v2 + v5) v8 ((v3 + v6) + v9))
  ∙ +Assoc ((v1 + v4) + v7) ((v2 + v5) + v8) ((v3 + v6) + v9)



-- test-mini：c2 两步正确版（m1 组内 Assoc + m2 组间 Assoc）
test-mini : ∀ (q v8 v3 v6 v9 : ℤ) →
  q + (v8 + (v3 + (v6 + v9))) ≡ q + ((v8 + (v3 + v6)) + v9)
test-mini q v8 v3 v6 v9 =
  let m1 : v3 + (v6 + v9) ≡ (v3 + v6) + v9
      m1 = assocP v3 v6 v9
      X1 = q + (v8 + (v3 + (v6 + v9)))
      X2 = q + (v8 + ((v3 + v6) + v9))
      p1 : X1 ≡ X2
      p1 = cong (λ w → q + (v8 + w)) m1
      p2 : X2 ≡ q + ((v8 + (v3 + v6)) + v9)
      p2 = cong (λ w → q + w) (+Assoc v8 (v3 + v6) v9)
  in p1 ∙ p2
