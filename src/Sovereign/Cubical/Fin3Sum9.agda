{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Cubical.Fin3Sum9 where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc)

assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)

postulate A2 B2 C2 Z : ℤ

-- test1：assocP 卡头应用作链段
test1 : A2 + (B2 + (C2 + Z)) ≡ (A2 + B2) + (C2 + Z)
test1 = assocP A2 B2 (C2 + Z)

-- test2：cong 包装后的卡头应用
test2 : ∀ (F : ℤ → ℤ) → F (A2 + (B2 + (C2 + Z))) ≡ F ((A2 + B2) + (C2 + Z))
test2 = λ F → cong F (assocP A2 B2 (C2 + Z))

-- test3：sym (assocP 卡头) 反向
test3 : (A2 + B2) + (C2 + Z) ≡ A2 + (B2 + (C2 + Z))
test3 = sym (assocP A2 B2 (C2 + Z))

-- test4：∙ 链中段的 assocP 组合（Fin3 38-42 段的精确缩影）