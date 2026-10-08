{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Algebra._ProbeAssoc where

open import Cubical.Data.Int using (ℤ; _+_; _·_)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm; ·DistR+; ·DistL+)

swap3 : ∀ p q r → p + (q + r) ≡ q + (p + r)
swap3 p q r = +Assoc p q r ∙ cong (_+ r) (+Comm p q) ∙ sym (+Assoc q p r)

bubble1 : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℤ) →
  v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + (v9)))))))) ≡ v1 + (v2 + (v4 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9))))))))
bubble1 v1 v2 v3 v4 v5 v6 v7 v8 v9 = cong (v1 +_) (cong (v2 +_) (swap3 v3 v4 (v5 + (v6 + (v7 + (v8 + (v9)))))))

bubble2 : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℤ) →
  v1 + (v2 + (v4 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9))))))))
bubble2 v1 v2 v3 v4 v5 v6 v7 v8 v9 = cong (v1 +_) (swap3 v2 v4 (v3 + (v5 + (v6 + (v7 + (v8 + (v9)))))))

bubble3 : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℤ) →
  v1 + (v4 + (v2 + (v3 + (v5 + (v6 + (v7 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v3 + (v5 + (v7 + (v6 + (v8 + (v9))))))))
bubble3 v1 v2 v3 v4 v5 v6 v7 v8 v9 = cong (v1 +_) (cong (v4 +_) (cong (v2 +_) (cong (v3 +_) (cong (v5 +_) (swap3 v6 v7 (v8 + (v9)))))))

bubble4 : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℤ) →
  v1 + (v4 + (v2 + (v3 + (v5 + (v7 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v3 + (v7 + (v5 + (v6 + (v8 + (v9))))))))
bubble4 v1 v2 v3 v4 v5 v6 v7 v8 v9 = cong (v1 +_) (cong (v4 +_) (cong (v2 +_) (cong (v3 +_) (swap3 v5 v7 (v6 + (v8 + (v9)))))))

bubble5 : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℤ) →
  v1 + (v4 + (v2 + (v3 + (v7 + (v5 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v2 + (v7 + (v3 + (v5 + (v6 + (v8 + (v9))))))))
bubble5 v1 v2 v3 v4 v5 v6 v7 v8 v9 = cong (v1 +_) (cong (v4 +_) (cong (v2 +_) (swap3 v3 v7 (v5 + (v6 + (v8 + (v9)))))))

bubble6 : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℤ) →
  v1 + (v4 + (v2 + (v7 + (v3 + (v5 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v3 + (v5 + (v6 + (v8 + (v9))))))))
bubble6 v1 v2 v3 v4 v5 v6 v7 v8 v9 = cong (v1 +_) (cong (v4 +_) (swap3 v2 v7 (v3 + (v5 + (v6 + (v8 + (v9)))))))

bubble7 : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℤ) →
  v1 + (v4 + (v7 + (v2 + (v3 + (v5 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v6 + (v8 + (v9))))))))
bubble7 v1 v2 v3 v4 v5 v6 v7 v8 v9 = cong (v1 +_) (cong (v4 +_) (cong (v7 +_) (cong (v2 +_) (swap3 v3 v5 (v6 + (v8 + (v9)))))))

bubble8 : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℤ) →
  v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v6 + (v8 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v8 + (v6 + (v9))))))))
bubble8 v1 v2 v3 v4 v5 v6 v7 v8 v9 = cong (v1 +_) (cong (v4 +_) (cong (v7 +_) (cong (v2 +_) (cong (v5 +_) (cong (v3 +_) (swap3 v6 v8 (v9)))))))

bubble9 : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℤ) →
  v1 + (v4 + (v7 + (v2 + (v5 + (v3 + (v8 + (v6 + (v9)))))))) ≡ v1 + (v4 + (v7 + (v2 + (v5 + (v8 + (v3 + (v6 + (v9))))))))
bubble9 v1 v2 v3 v4 v5 v6 v7 v8 v9 = cong (v1 +_) (cong (v4 +_) (cong (v7 +_) (cong (v2 +_) (cong (v5 +_) (swap3 v3 v8 (v6 + (v9)))))))


-- gather 2 步版（已验证绿）
gather : ∀ a x y z → ((a · x) + (a · y)) + (a · z) ≡ a · ((x + y) + z)
gather a x y z =
      cong (_+ (a · z)) (sym (·DistR+ a x y))
  ∙ sym (·DistR+ a (x + y) z)

-- rearrange9
rearrange9 : ∀ (a₁ a₂ a₃ q1 q2 q3 q4 q5 q6 q7 q8 q9 : ℤ) →
  ((((a₁ · q1) + (a₂ · q2)) + (a₃ · q3)) + (((a₁ · q4) + (a₂ · q5)) + (a₃ · q6))) + (((a₁ · q7) + (a₂ · q8)) + (a₃ · q9))
  ≡ ((a₁ · ((q1 + q4) + q7)) + (a₂ · ((q2 + q5) + q8))) + (a₃ · ((q3 + q6) + q9))
rearrange9 a₁ a₂ a₃ q1 q2 q3 q4 q5 q6 q7 q8 q9 = ?
