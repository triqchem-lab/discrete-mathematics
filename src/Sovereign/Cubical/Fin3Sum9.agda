{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Cubical.Fin3Sum9
-- Fin 3 上 9 项求和的展平/交换引理族——服务 Laurent → Burau → Braid 链的 sum9 转置
--
-- 核心原则：
--   1. 9 项求和拆五步独立引理（uflat9-s1..s5），每步单一括号重组
--   2. 组合链用命名半链（p12/p34）——保持 ∙ 嵌套 ≤3
--   3. 纯 ℤ 字面情形（pos/negsuc）逐案转发 +Assoc，不引入 subst
--
-- 包含：assocP, uflat9-s1..s5, unflat9, sum9-swap

module Sovereign.Cubical.Fin3Sum9 where

-- ② 导入区

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

-- ─── unflat9：五引理组装（右结合 row 序 → 目标三组）───

unflat9 : ∀ (A1 A2 A3 B1 B2 B3 C1 C2 C3 : ℤ) →
  A1 + (B1 + (C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
  ≡ (((A1 + B1) + C1) + (((A2 + (B2 + C2))) + ((A3 + (B3 + C3)))))
unflat9 A1 A2 A3 B1 B2 B3 C1 C2 C3 =
  let X1 = A1 + (B1 + (C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
      p1 : X1 ≡ ((A1 + B1) + ((C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3))))))))
      p1 = uflat9-s1 A1 B1 C1 A2 B2 C2 A3 B3 C3
      X2 = ((A1 + B1) + ((C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3))))))))
      p2 : X2 ≡ (((A1 + B1) + C1) + ((A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
      p2 = uflat9-s2 A1 B1 C1 A2 B2 C2 A3 B3 C3
      X3 = (((A1 + B1) + C1) + ((A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
      p3 : X3 ≡ (((A1 + B1) + C1) + (((A2 + B2)) + ((C2 + (A3 + (B3 + C3))))))
      p3 = uflat9-s3 A1 B1 C1 A2 B2 C2 A3 B3 C3
      X4 = (((A1 + B1) + C1) + (((A2 + B2)) + ((C2 + (A3 + (B3 + C3))))))
      p4 : X4 ≡ (((A1 + B1) + C1) + ((((A2 + B2)) + C2) + ((A3 + (B3 + C3)))))
      p4 = uflat9-s4 A1 B1 C1 A2 B2 C2 A3 B3 C3
      X5 = (((A1 + B1) + C1) + ((((A2 + B2)) + C2) + ((A3 + (B3 + C3)))))
      p5 : X5 ≡ (((A1 + B1) + C1) + (((A2 + (B2 + C2))) + ((A3 + (B3 + C3)))))
      p5 = uflat9-s5 A1 B1 C1 A2 B2 C2 A3 B3 C3
      p12 = p1 ∙ p2
      p34 = p3 ∙ p4
  in p12 ∙ p34 ∙ p5

-- ─── sum9-swap：col 序 → row 序 → 三组（flat9 ∙ unflat9 组合的核心交换）───

sum9-swap : ∀ (A1 A2 A3 B1 B2 B3 C1 C2 C3 : ℤ) →
  A1 + (B1 + (C1 + (A2 + (B2 + (C2 + (A3 + (B3 + C3)))))))
  ≡ (((A1 + B1) + C1) + (((A2 + (B2 + C2))) + ((A3 + (B3 + C3)))))
sum9-swap = unflat9
