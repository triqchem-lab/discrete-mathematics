{-# OPTIONS --cubical --guardedness #-}
-- | Sovereign.Cubical.Fin3
-- Fin 3 上的求和交换/分配引理——服务 Laurent → Burau → Braid 链

module Sovereign.Cubical.Fin3 where
--
-- 核心原则：
-- 1. sum3 定义为右结合（f0 + (f1 + f2)）
-- 2. sum3-comm 是 3×3 求和转置（9 项交换——非简单 Assoc 可闭合）
-- 3. sum3-distribˡ 已绿（·DistR+ 两步链）
--
-- 包含：sum3、sum3-comm（WIP）、sum3-distribˡ（绿）

open import Cubical.Data.Fin using (Fin; fzero; fsuc)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; _+_; _·_; pos; negsuc)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm; ·DistR+)

sum3 : (Fin 3 → ℤ) → ℤ
sum3 f = f fzero + (f (fsuc fzero) + f (fsuc (fsuc fzero)))

+interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+interchange a b c d =
      sym (+Assoc a b (c + d))
  ∙ cong (a +_) (+Assoc b c d)
  ∙ cong (λ w → a + (w + d)) (+Comm b c)
  ∙ cong (a +_) (sym (+Assoc c b d))
  ∙ +Assoc a c (b + d)

sum3-ext : ∀ (f g : Fin 3 → ℤ) → (∀ x → f x ≡ g x) → sum3 f ≡ sum3 g
sum3-ext f g h = cong₂ _+_ (h fzero) (cong₂ _+_ (h (fsuc fzero)) (h (fsuc (fsuc fzero))))

-- ─── sum3-distribˡ ✓ 绿 ───

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
  (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + v9)))))))) ≡ (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + v9))))))))
bubble9 v1 v2 v3 v4 v5 v6 v7 v8 v9 = refl

sum3-distribˡ : ∀ (a : ℤ) (f : Fin 3 → ℤ) →
  a · sum3 f ≡ sum3 (λ k → a · f k)
sum3-distribˡ a f =
      ·DistR+ a (f fzero) ((f (fsuc fzero)) + (f (fsuc (fsuc fzero))))
  ∙ cong ((a · f fzero) +_) (·DistR+ a (f (fsuc fzero)) (f (fsuc (fsuc fzero))))

-- ─── sum3-comm WIP —— 需要 15 步 +Assoc/+Comm 链 （见 proof_dag Fin3.sum3-comm-t4） ───
-- 待方案：A) 非 cubical 模块用 solve-∀（stdlib Data.Integer.Tactic.RingSolver）+B·传输桥
--        B) ≡-Reasoning 逐步组合 +Assoc/+Comm 引理（~15 步）
--        C) 自建 normalize-to-canonical 函数 + refl

sum3-comm : ∀ (f : Fin 3 → Fin 3 → ℤ) →
  sum3 (λ k → sum3 (λ l → f k l)) ≡ sum3 (λ l → sum3 (λ k → f k l))
sum3-comm f =
  let
      e1 : ((f fzero fzero) + ((f fzero (fsuc fzero)) + (f fzero (fsuc (fsuc fzero))))) + (((f (fsuc fzero) fzero) + ((f (fsuc fzero) (fsuc fzero)) + (f (fsuc fzero) (fsuc (fsuc fzero))))) + ((f (fsuc (fsuc fzero)) fzero) + ((f (fsuc (fsuc fzero)) (fsuc fzero)) + (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero)))))) ≡ ((f fzero fzero) + ((f fzero (fsuc fzero)) + ((f fzero (fsuc (fsuc fzero))) + ((f (fsuc fzero) fzero) + ((f (fsuc fzero) (fsuc fzero)) + ((f (fsuc fzero) (fsuc (fsuc fzero))) + ((f (fsuc (fsuc fzero)) fzero) + ((f (fsuc (fsuc fzero)) (fsuc fzero)) + (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero)))))))))))
      e1 = cong ((f fzero fzero) +_) (cong ((f fzero (fsuc fzero)) +_) (sym (+Assoc (f fzero (fsuc (fsuc fzero))) (f (fsuc fzero) fzero) ((f (fsuc fzero) (fsuc fzero)) + ((f (fsuc fzero) (fsuc (fsuc fzero))) + ((f (fsuc (fsuc fzero)) fzero) + ((f (fsuc (fsuc fzero)) (fsuc fzero)) + (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))))))))))
      bb : ((f fzero fzero) + ((f fzero (fsuc fzero)) + ((f fzero (fsuc (fsuc fzero))) + ((f (fsuc fzero) fzero) + ((f (fsuc fzero) (fsuc fzero)) + ((f (fsuc fzero) (fsuc (fsuc fzero))) + ((f (fsuc (fsuc fzero)) fzero) + ((f (fsuc (fsuc fzero)) (fsuc fzero)) + (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))))))))))) ≡ ((f fzero fzero) + ((f (fsuc fzero) fzero) + ((f (fsuc (fsuc fzero)) fzero) + ((f fzero (fsuc fzero)) + ((f (fsuc fzero) (fsuc fzero)) + ((f (fsuc (fsuc fzero)) (fsuc fzero)) + ((f fzero (fsuc (fsuc fzero))) + ((f (fsuc fzero) (fsuc (fsuc fzero))) + (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero)))))))))))
      bb = bubble1 (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero))) (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero))) (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))) ∙ bubble2 (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero))) (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero))) (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))) ∙ bubble3 (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero))) (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero))) (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))) ∙ bubble4 (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero))) (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero))) (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))) ∙ bubble5 (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero))) (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero))) (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))) ∙ bubble6 (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero))) (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero))) (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))) ∙ bubble7 (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero))) (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero))) (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))) ∙ bubble8 (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero))) (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero))) (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))) ∙ bubble9 (f fzero fzero) (f fzero (fsuc fzero)) (f fzero (fsuc (fsuc fzero))) (f (fsuc fzero) fzero) (f (fsuc fzero) (fsuc fzero)) (f (fsuc fzero) (fsuc (fsuc fzero))) (f (fsuc (fsuc fzero)) fzero) (f (fsuc (fsuc fzero)) (fsuc fzero)) (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero)))
      c1 : ((f fzero fzero) + ((f (fsuc fzero) fzero) + ((f (fsuc (fsuc fzero)) fzero) + ((f fzero (fsuc fzero)) + ((f (fsuc fzero) (fsuc fzero)) + ((f (fsuc (fsuc fzero)) (fsuc fzero)) + ((f fzero (fsuc (fsuc fzero))) + ((f (fsuc fzero) (fsuc (fsuc fzero))) + (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero))))))))))) ≡ (((f fzero fzero) + ((f (fsuc fzero) fzero) + (f (fsuc (fsuc fzero)) fzero))) + (((f fzero (fsuc fzero)) + ((f (fsuc fzero) (fsuc fzero)) + (f (fsuc (fsuc fzero)) (fsuc fzero)))) + ((f fzero (fsuc (fsuc fzero))) + ((f (fsuc fzero) (fsuc (fsuc fzero))) + (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero)))))))
      c1 = cong ((f fzero fzero) +_) (+Assoc (f (fsuc fzero) fzero) (f (fsuc (fsuc fzero)) fzero) ((f fzero (fsuc fzero)) + ((f (fsuc fzero) (fsuc fzero)) + ((f (fsuc (fsuc fzero)) (fsuc fzero)) + ((f fzero (fsuc (fsuc fzero))) + ((f (fsuc fzero) (fsuc (fsuc fzero))) + (f (fsuc (fsuc fzero)) (fsuc (fsuc fzero)))))))))
  in e1 ∙ bb ∙ c1
