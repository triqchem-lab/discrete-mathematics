{-# OPTIONS --cubical --guardedness #-}
module ProbeA where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc)

-- sum3-expand：三组列形 → 9 项右结合（4 步 sym +Assoc 逐叶右化）
sum3-expand : ∀ (a00 a01 a02 a10 a11 a12 a20 a21 a22 : ℤ) →
  (a00 + (a01 + a02)) + ((a10 + (a11 + a12)) + (a20 + (a21 + a22)))
  ≡ a00 + (a01 + (a02 + (a10 + (a11 + (a12 + (a20 + (a21 + a22)))))))
sum3-expand a00 a01 a02 a10 a11 a12 a20 a21 a22 =
  let Y = a10 + (a11 + a12)
      Z = a20 + (a21 + a22)
      e1 : (a00 + (a01 + a02)) + (Y + Z) ≡ a00 + ((a01 + a02) + (Y + Z))
      e1 = sym (+Assoc a00 (a01 + a02) (Y + Z))
      e2 : a00 + ((a01 + a02) + (Y + Z)) ≡ a00 + (a01 + (a02 + (Y + Z)))
      e2 = cong (a00 +_) (sym (+Assoc a01 a02 (Y + Z)))
      e3 : a00 + (a01 + (a02 + (Y + Z))) ≡ a00 + (a01 + (a02 + (a10 + ((a11 + a12) + Z))))
      e3 = cong (λ w → a00 + (a01 + (a02 + w))) (sym (+Assoc a10 (a11 + a12) Z))
      e4 : a00 + (a01 + (a02 + (a10 + ((a11 + a12) + Z)))) ≡ a00 + (a01 + (a02 + (a10 + (a11 + (a12 + Z)))))
      e4 = cong (λ w → a00 + (a01 + (a02 + (a10 + w)))) (sym (+Assoc a11 a12 Z))
  in e1 ∙ e2 ∙ e3 ∙ e4
