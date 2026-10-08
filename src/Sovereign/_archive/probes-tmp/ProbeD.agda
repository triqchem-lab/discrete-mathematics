{-# OPTIONS --cubical --guardedness #-}
module ProbeD where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm)

-- test-s3：interchange s3 最小复现
test-s3 : ∀ (a b c d : ℤ) → a + ((b + c) + d) ≡ a + ((c + b) + d)
test-s3 a b c d = cong (λ w → a + (w + d)) (+Comm b c)
