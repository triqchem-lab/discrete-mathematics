{-# OPTIONS --cubical --guardedness #-}
module ProbeJ where

open import Cubical.Data.Fin using (Fin; fzero; fsuc)
open import Cubical.Data.Int using (ℤ; _+_)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm)

sum3 : (Fin 3 → ℤ) → ℤ
sum3 f = f fzero + (f (fsuc fzero) + f (fsuc (fsuc fzero)))

sum3-comm : ∀ (f : Fin 3 → Fin 3 → ℤ) →
  sum3 (λ k → sum3 (λ l → f k l)) ≡ sum3 (λ l → sum3 (λ k → f k l))
-- [归档注记 2026-10-11] WIP 草稿洞——**无形式化保证**（诊断探针合法草稿态）；
--   sum3-comm 命题本体已在 src 以 Fin3 rearrange 路线解决（历史假绿事故案——见 README）。
sum3-comm f = {!!}
