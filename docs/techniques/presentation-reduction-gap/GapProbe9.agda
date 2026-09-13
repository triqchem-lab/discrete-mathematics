-- ⑨ 决定性实验：声明 REWRITE 后，普遍定律能否自动成立（写成 λ x → refl）
{-# OPTIONS --rewriting #-}
module GapProbe9 where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite
open import T3 using (T3; step)
postulate d3-law : ∀ x → step (step (step x)) ≡ x
{-# REWRITE d3-law #-}
auto-lam : ∀ x → step (step (step x)) ≡ x
auto-lam = λ x → refl
