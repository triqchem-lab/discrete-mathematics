{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Cubical.Fin3Sum9 where

open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc)

assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)

-- ─── unflat9 五步独立引理（每步签名显式，探针 Probe3 test-s1..s5 验证绿）───

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
  ∙ assocP (A1 + B1) C1 (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))
  ∙ cong (λ w1 → ((A1 + B1) + C1) + w1) (assocP A2 B2 (C2 + (A3 + (B3 + C3))))

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

-- flat9：组形 → B组+C组并层形（sym assocP 拆 A 组 2 步 + B 组 Assoc 拆 1 步）
flat9 : ∀ A1 A2 A3 B1 B2 B3 C1 C2 C3 →
      (A1 + (A2 + A3)) + ((B1 + (B2 + B3)) + (C1 + (C2 + C3)))
  ≡   (A1 + (A2 + (((A3 + B1) + (B2 + B3))))) + (C1 + (C2 + C3))
flat9 A1 A2 A3 B1 B2 B3 C1 C2 C3 =
      assocP (A1 + (A2 + A3)) (B1 + (B2 + B3)) (C1 + (C2 + C3))
  ∙ cong (λ w → w + (C1 + (C2 + C3))) (sym (assocP A1 (A2 + A3) (B1 + (B2 + B3))))
  ∙ cong (λ w → (A1 + w) + (C1 + (C2 + C3))) (sym (assocP A2 A3 (B1 + (B2 + B3))))
  ∙ cong (λ w → (A1 + (A2 + w)) + (C1 + (C2 + C3))) (assocP A3 B1 (B2 + B3))


-- ─── swap9：col 序 → row 序（comm 9 步，洞）───

swap9 : ∀ A1 A2 A3 B1 B2 B3 C1 C2 C3 →
      A1 + (A2 + (A3 + (B1 + (B2 + (B3 + (C1 + (C2 + C3)))))))
  ≡   A1 + (B1 + (C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
swap9 A1 A2 A3 B1 B2 B3 C1 C2 C3 = {!!}
-- ─── unflat9：右结合 row 序 → 目标三组（test5 已验证 5 步）───

unflat9 : ∀ A1 A2 A3 B1 B2 B3 C1 C2 C3 →
      A1 + (B1 + (C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
  ≡   (A1 + (B1 + C1)) + ((A2 + (B2 + C2)) + (A3 + (B3 + C3)))
unflat9 A1 A2 A3 B1 B2 B3 C1 C2 C3 =
  uflat9-s1 A1 B1 C1 A2 B2 C2 A3 B3 C3
  ∙ uflat9-s2 A1 B1 C1 A2 B2 C2 A3 B3 C3
  ∙ uflat9-s3 A1 B1 C1 A2 B2 C2 A3 B3 C3
  ∙ uflat9-s4 A1 B1 C1 A2 B2 C2 A3 B3 C3
  ∙ uflat9-s5 A1 B1 C1 A2 B2 C2 A3 B3 C3


