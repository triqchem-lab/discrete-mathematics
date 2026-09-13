-- ②b（正确形态）无 REWRITE 时，普遍定律能否靠归一化器闭合？
module GapProbe2b where
open import Agda.Builtin.Equality using (_≡_; refl)
open import T3 using (T3; step)
law : ∀ x → step (step (step x)) ≡ x
law = λ x → refl
