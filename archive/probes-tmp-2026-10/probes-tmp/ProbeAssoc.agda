{-# OPTIONS --cubical --guardedness #-}
module ProbeAssoc where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym)
open import Cubical.Data.Int.Properties using (+Assoc)

assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)

-- 卡头 z 的应用是否类型完整
test : ∀ (a b c : ℤ) → a + (b + c) ≡ (a + b) + c
test = assocP
