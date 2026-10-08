{-# OPTIONS --cubical --guardedness #-}
-- | Sovereign.Cubical.Fin3
-- Fin 3 上的求和交换/分配引理——服务 Laurent → Burau → Braid 链
--
-- 核心原则：
-- 1. sum3 定义为右结合（f0 + (f1 + f2)）
-- 2. +interchange 是 3×3 求和转置的关键引理（5 步 ✓）
-- 3. sum3-distribˡ 已绿（·DistR+ 两步链）
--
-- 包含：sum3、sum3-ext、sum3-distribˡ（绿）、+interchange（绿）、sum3-comm（WIP）


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

-- ── sum3-comm WIP ──

sum3-comm : ∀ (f : Fin 3 → Fin 3 → ℤ) →
  sum3 (λ k → sum3 (λ l → f k l)) ≡ sum3 (λ l → sum3 (λ k → f k l))
sum3-comm f = cong (f fzero fzero +_) inner
  where
    inner : (f fzero (fsuc fzero) + f fzero (fsuc (fsuc fzero)))
          + (((f (fsuc fzero) fzero) + ((f (fsuc fzero) (fsuc fzero)) + (f (fsuc fzero) (fsuc (fsuc fzero)))))
          + (((f (fsuc (fsuc fzero)) fzero) + ((f (fsuc (fsuc fzero)) (fsuc fzero)) + (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero)))))))
          ≡ (f (fsuc fzero) fzero + (f (fsuc (fsuc fzero)) fzero))
          + (((f fzero (fsuc fzero)) + ((f (fsuc fzero) (fsuc fzero)) + (f (fsuc (fsuc fzero)) (fsuc fzero))))
          + ((f fzero (fsuc (fsuc fzero))) + ((f (fsuc fzero) (fsuc (fsuc fzero))) + (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))))))
    inner = +interchange
          ((f fzero (fsuc fzero)) + (f fzero (fsuc (fsuc fzero))))
          ((f (fsuc fzero) fzero) + ((f (fsuc fzero) (fsuc fzero)) + (f (fsuc fzero) (fsuc (fsuc fzero)))))
          ((f (fsuc (fsuc fzero)) fzero) + ((f (fsuc (fsuc fzero)) (fsuc fzero)) + (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero)))))
          {!!}
