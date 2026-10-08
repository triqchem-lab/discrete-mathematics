{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Cubical.Fin3Sum9 where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc)

assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)

-- ─── unflat9 五步独立引理（探针 Probe3 test-s1..s5 已验证全绿）───

uflat9-s1 : ∀ (A1 B1 C1 A2 B2 C2 A3 B3 C3 : ℤ) →
  A1 + (B1 + (C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
  ≡ ((A1 + B1) + ((C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3))))))))
uflat9-s1 A1 B1 C1 A2 B2 C2 A3 B3 C3 =
      assocP A1 B1 (C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3))))))

uflat9-s2 : ∀ (A1 B1 C1 A2 B2 C2 A3 B3 C3 : ℤ) →
  ((A1 + B1) + ((C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3))))))))
  ≡ (((A1 + B1) + C1) + ((A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
uflat9-s2 A1 B1 C1 A2 B2 C2 A3 B3 C3 =
      assocP (A1 + B1) C1 (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))

uflat9-s3 : ∀ (A1 B1 C1 A2 B2 C2 A3 B3 C3 : ℤ) →
  (((A1 + B1) + C1) + ((A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
  ≡ (((A1 + B1) + C1) + (((A2 + B2)) + ((C2 + (A3 + (B3 + C3))))))
uflat9-s3 A1 B1 C1 A2 B2 C2 A3 B3 C3 =
      cong (λ w1 → ((A1 + B1) + C1) + w1) (assocP A2 B2 (C2 + (A3 + (B3 + C3))))

uflat9-s4 : ∀ (A1 B1 C1 A2 B2 C2 A3 B3 C3 : ℤ) →
  (((A1 + B1) + C1) + (((A2 + B2)) + ((C2 + (A3 + (B3 + C3))))))
  ≡ (((A1 + B1) + C1) + ((((A2 + B2)) + C2) + ((A3 + (B3 + C3)))))
uflat9-s4 A1 B1 C1 A2 B2 C2 A3 B3 C3 =
      cong (λ w1 → ((A1 + B1) + C1) + w1) (assocP (A2 + B2) C2 (A3 + (B3 + C3)))

uflat9-s5 : ∀ (A1 B1 C1 A2 B2 C2 A3 B3 C3 : ℤ) →
  (((A1 + B1) + C1) + ((((A2 + B2)) + C2) + ((A3 + (B3 + C3)))))
  ≡ (((A1 + B1) + C1) + (((A2 + (B2 + C2))) + ((A3 + (B3 + C3)))))
uflat9-s5 A1 B1 C1 A2 B2 C2 A3 B3 C3 =
      cong (λ w2 → ((A1 + B1) + C1) + ((w2 + (A3 + (B3 + C3))))) (sym (assocP A2 B2 C2))

-- ─── unflat9 五步独立引理（每步签名显式，探针 Probe3 test-s1..s5 验证绿）───
