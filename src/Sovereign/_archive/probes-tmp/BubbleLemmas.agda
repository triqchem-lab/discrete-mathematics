{-# OPTIONS --cubical --guardedness #-}
module BubbleLemmas where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm)

assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)

swap3 : ∀ p q r → p + (q + r) ≡ q + (p + r)
swap3 p q r = +Assoc p q r ∙ cong (_+ r) (+Comm p q) ∙ sym (+Assoc q p r)

v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℤ
v1 = pos 1
v2 = pos 2
v3 = pos 3
v4 = pos 4
v5 = pos 5
v6 = pos 6
v7 = pos 7
v8 = pos 8
v9 = pos 9

bubble1 : v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + (v9)))))))) ≡ v1 + (v2 + (v4 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9))))))))
bubble1 = cong (v1 +_) (cong (v2 +_) (swap3 v3 v4 (v5 + (v6 + (v7 + (v8 + (v9)))))))

bubble2 : v1 + (v2 + (v4 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9))))))))
bubble2 = cong (v1 +_) (swap3 v2 v4 (v3 + (v5 + (v6 + (v7 + (v8 + (v9)))))))

bubble3 : v1 + (v4 + (v2 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v3 + (v5 + (v7 + (v6 + (v8 + (v9))))))))
bubble3 = cong (v1 +_) (cong (v4 +_) (cong (v2 +_) (cong (v3 +_) (cong (v5 +_) (swap3 v6 v7 (v8 + (v9)))))))

bubble4 : v1 + (v4 + (v2 + (v3 + (v5 + (v7 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v3 + (v7 + (v5 + (v6 + (v8 + (v9))))))))
bubble4 = cong (v1 +_) (cong (v4 +_) (cong (v2 +_) (cong (v3 +_) (swap3 v5 v7 (v6 + (v8 + (v9)))))))

bubble5 : v1 + (v4 + (v2 + (v3 + (v7 + (v5 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v7 + (v3 + (v5 + (v6 + (v8 + (v9))))))))
bubble5 = cong (v1 +_) (cong (v4 +_) (cong (v2 +_) (swap3 v3 v7 (v5 + (v6 + (v8 + (v9)))))))

bubble6 : v1 + (v4 + (v2 + (v7 + (v3 + (v5 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v3 + (v5 + (v6 + (v8 + (v9))))))))
bubble6 = cong (v1 +_) (cong (v4 +_) (swap3 v2 v7 (v3 + (v5 + (v6 + (v8 + (v9)))))))

bubble7 : v1 + (v4 + (v7 + (v2 + (v3 + (v5 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v6 + (v8 + (v9))))))))
bubble7 = cong (v1 +_) (cong (v4 +_) (cong (v7 +_) (cong (v2 +_) (swap3 v3 v5 (v6 + (v8 + (v9)))))))

bubble8 : v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v8 + (v6 + (v9))))))))
bubble8 = cong (v1 +_) (cong (v4 +_) (cong (v7 +_) (cong (v2 +_) (cong (v5 +_) (cong (v3 +_) (swap3 v6 v8 (v9)))))))

bubble9 : v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v8 + (v6 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v5 + (v8 + (v3 + (v6 + (v9))))))))
bubble9 = cong (v1 +_) (cong (v4 +_) (cong (v7 +_) (cong (v2 +_) (cong (v5 +_) (swap3 v3 v8 (v6 + (v9)))))))
