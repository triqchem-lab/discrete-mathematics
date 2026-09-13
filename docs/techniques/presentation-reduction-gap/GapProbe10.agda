-- ⑩ 决定性：生成元是 **postulate（抽象，展示群形态）** 时，REWRITE 规则能否**生效**
{-# OPTIONS --rewriting #-}
module GapProbe10 where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite
postulate
  A : Set
  d : A → A
  law : ∀ x → d (d (d x)) ≡ x
{-# REWRITE law #-}
auto-abstract : ∀ x → d (d (d x)) ≡ x
auto-abstract = λ x → refl
