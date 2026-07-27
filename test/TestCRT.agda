{-# OPTIONS --cubical --guardedness #-}
module TestCRT where
open import Data.Nat using (ℕ; _<_; _+_; _*_; _%_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Cubical.Foundations.Prelude using (PathP; refl)
open import Cubical.Data.Sigma.Properties using (ΣPathP)

-- 测试: 直接使用 PathP 和 refl
test : (p : Σ ℕ (λ x → x < 3)) → PathP (λ _ → Σ ℕ (λ x → x < 3)) p p
test p = refl
