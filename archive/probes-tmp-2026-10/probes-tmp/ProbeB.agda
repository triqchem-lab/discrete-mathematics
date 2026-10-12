{-# OPTIONS --cubical --guardedness #-}
module ProbeB where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc)

assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)

-- test-where：与 Fin3Sum9 同款结构但放 where 块内
test-outer : ∀ (q v8 v3 v6 v9 : ℤ) →
  q + (v8 + (v3 + (v6 + v9))) ≡ q + (((v8 + (v3 + v6)) + v9))
test-outer q v8 v3 v6 v9 = test-inner q v8 v3 v6 v9
  where
  test-inner : ∀ (q v8 v3 v6 v9 : ℤ) →
    q + (v8 + (v3 + (v6 + v9))) ≡ q + (((v8 + (v3 + v6)) + v9))
  test-inner q v8 v3 v6 v9 =
    let m1 : v3 + (v6 + v9) ≡ (v3 + v6) + v9
        m1 = assocP v3 v6 v9
        X1 = q + (v8 + (v3 + (v6 + v9)))
        X2 = q + (v8 + ((v3 + v6) + v9))
        p1 : X1 ≡ X2
        p1 = cong (λ w → q + (v8 + w)) m1
        p2 : X2 ≡ q + ((v8 + (v3 + v6)) + v9)
        p2 = cong (λ w → q + w) (+Assoc v8 (v3 + v6) v9)
    in p1 ∙ p2
