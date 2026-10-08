{-# OPTIONS --cubical --guardedness #-}
-- | Sovereign.Cubical.Fin3
-- Fin 3 上的求和交换/分配引理——服务 Laurent → Burau → Braid 链
--
-- 核心原则：
-- 1. sum3 定义为右结合（f0 + (f1 + f2)）
-- 2. +interchange 是 3×3 求和转置的关键引理（5 步 ✓）
-- 3. sum3-distribˡ 已绿（·DistR+ 两步链）
--
-- 包含：sum3、sum3-ext、sum3-distribˡ（绿）、+interchange（绿）、sum3-comm（完整 17+ 步链已绿）


module Sovereign.Cubical.Fin3 where
open import Cubical.Data.Fin using (Fin; fzero; fsuc)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; _+_; _·_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm; ·DistR+)

sum3 : (Fin 3 → ℤ) → ℤ
sum3 f = f fzero + (f (fsuc fzero) + f (fsuc (fsuc fzero)))

sum3-ext : ∀ (f g : Fin 3 → ℤ) → (∀ x → f x ≡ g x) → sum3 f ≡ sum3 g
sum3-ext f g h = cong₂ _+_ (h fzero) (cong₂ _+_ (h (fsuc fzero)) (h (fsuc (fsuc fzero))))

-- ── sum3-distribˡ ✓ ──

sum3-distribˡ : ∀ (a : ℤ) (f : Fin 3 → ℤ) →
  a · sum3 f ≡ sum3 (λ k → a · f k)
sum3-distribˡ a f =
      ·DistR+ a (f fzero) ((f (fsuc fzero)) + (f (fsuc (fsuc fzero))))
  ∙ cong ((a · f fzero) +_) (·DistR+ a (f (fsuc fzero)) (f (fsuc (fsuc fzero))))

-- ── +interchange ✓ 5 步 ──

+interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+interchange a b c d =
      sym (+Assoc a b (c + d))
  ∙ cong (a +_) (+Assoc b c d)
  ∙ cong (λ w → a + (w + d)) (+Comm b c)
  ∙ cong (a +_) (sym (+Assoc c b d))
  ∙ +Assoc a c (b + d)

-- ── sum3-comm（已完整：f1-f4 展平 + bubble 重排 + rg1-4 收拢 + in 链）──

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


sum3-comm : ∀ (f : Fin 3 → Fin 3 → ℤ) →
  sum3 (λ k → sum3 (λ l → f k l)) ≡ sum3 (λ l → sum3 (λ k → f k l))
sum3-comm f =
  let
    p1 = f fzero fzero
    p2 = f fzero (fsuc fzero)
    p3 = f fzero (fsuc (fsuc fzero))
    p4 = f (fsuc fzero) fzero
    p5 = f (fsuc fzero) (fsuc fzero)
    p6 = f (fsuc fzero) (fsuc (fsuc fzero))
    p7 = f (fsuc (fsuc fzero)) fzero
    p8 = f (fsuc (fsuc fzero)) (fsuc fzero)
    p9 = f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))
    -- 展平 6 步（从 ((C1+C2)+C3) 到全右）
    -- 展平步1: 解开 X=(p1+(p2+p3)) 内层
    f1 = sym (+Assoc p1 (p2 + p3) ((p4 + (p5 + p6)) + (p7 + (p8 + p9))))
    -- 展平步2: 解开 (p2+p3)
    f2 = cong (p1 +_) (sym (+Assoc p2 p3 ((p4 + (p5 + p6)) + (p7 + (p8 + p9)))))
    -- 展平步3: 解开 Y=(p4+(p5+p6))
    f3 = cong (p1 +_) (cong (p2 +_) (cong (p3 +_) (sym (+Assoc p4 (p5 + p6) (p7 + (p8 + p9))))))
    -- 展平步4: 解开 (p5+p6)
    f4 = cong (p1 +_) (cong (p2 +_) (cong (p3 +_) (cong (p4 +_) (sym (+Assoc p5 p6 (p7 + (p8 + p9)))))))
    rg1 = cong (p1 +_) (+Assoc p4 p7 (p2 + (p5 + (p8 + (p3 + (p6 + p9))))))
    rg2 = +Assoc p1 (p4 + p7) (p2 + (p5 + (p8 + (p3 + (p6 + p9)))))
    rg3 = cong (λ w → (p1 + (p4 + p7)) + w) (cong (p2 +_) (+Assoc p5 p8 (p3 + (p6 + p9))))
    rg4 = cong (λ w → (p1 + (p4 + p7)) + w) (+Assoc p2 (p5 + p8) (p3 + (p6 + p9)))

  in f1 ∙ f2 ∙ f3 ∙ f4 ∙ bubble1 p1 p2 p3 p4 p5 p6 p7 p8 p9 ∙ bubble2 p1 p2 p3 p4 p5 p6 p7 p8 p9 ∙ bubble3 p1 p2 p3 p4 p5 p6 p7 p8 p9 ∙ bubble4 p1 p2 p3 p4 p5 p6 p7 p8 p9 ∙ bubble5 p1 p2 p3 p4 p5 p6 p7 p8 p9 ∙ bubble6 p1 p2 p3 p4 p5 p6 p7 p8 p9 ∙ bubble7 p1 p2 p3 p4 p5 p6 p7 p8 p9 ∙ bubble8 p1 p2 p3 p4 p5 p6 p7 p8 p9 ∙ bubble9 p1 p2 p3 p4 p5 p6 p7 p8 p9 ∙ rg1 ∙ rg2 ∙ rg3 ∙ rg4