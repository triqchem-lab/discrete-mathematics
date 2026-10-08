{-# OPTIONS --cubical --guardedness #-}
module ProbeC where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm)

assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)

swap3 : ∀ p q r → p + (q + r) ≡ q + (p + r)
swap3 p q r = +Assoc p q r ∙ cong (_+ r) (+Comm p q) ∙ sym (+Assoc q p r)

-- test-tail：c3 终点 → 三组行形（m1 提出 + m2 两步 + m3 组内——全 1 层 lambda）
test-tail : ∀ (q v2 v5 v3 v8 v6 v9 : ℤ) →
  q + (v2 + (v5 + (v3 + (v8 + (v6 + v9))))) ≡ q + ((((v2 + v5) + v8)) + (((v3 + v6)) + v9))
test-tail q v2 v5 v3 v8 v6 v9 =
  let m1 : v3 + (v8 + (v6 + v9)) ≡ v8 + (v3 + (v6 + v9))
      m1 = swap3 v3 v8 (v6 + v9)
      X1 = q + (v2 + (v5 + (v3 + (v8 + (v6 + v9)))))
      p1 : X1 ≡ q + (v2 + (v5 + (v8 + (v3 + (v6 + v9)))))
      p1 = cong (λ w → q + (v2 + (v5 + w))) m1
      X2 = q + (v2 + (v5 + (v8 + (v3 + (v6 + v9)))))
      m2a : v3 + (v6 + v9) ≡ (v3 + v6) + v9
      m2a = assocP v3 v6 v9
      p2 : X2 ≡ q + (v2 + (v5 + (v8 + ((v3 + v6) + v9)))) 
      p2 = cong (λ w → q + (v2 + (v5 + (v8 + w)))) m2a
      X3 = q + ((((v2 + v5) + v8)) + (((v3 + v6)) + v9))
      m2b : v2 + (v5 + ((v8 + ((v3 + v6)) + v9))) ≡ (v2 + v5) + (v8 + ((v3 + v6) + v9))
      p3 : X3 ≡ q + ((((v2 + v5) + v8)) + (((v3 + v6)) + v9))
      p3 = cong (λ w → q + w) m2c
      m2c : (v2 + v5) + (v8 + ((v3 + v6) + v9)) ≡ ((v2 + v5) + v8) + ((v3 + v6) + v9)
      m2c = +Assoc (v2 + v5) v8 ((v3 + v6) + v9)
      p4 = m2c
  in p1 ∙ p2 ∙ p3 ∙ p4
