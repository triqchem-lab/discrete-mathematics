-- ③b **具体实例**：投影能归约到 step ⇒ 但仍需 3 个 case（= 穷举的来历）
module GapProbe3b where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import T3 using (T3; t0; t1; t2; step)
record Pres : Set₁ where
  field A : Set; d : A → A; e : A
inst : Pres
inst = record { A = T3 ; d = step ; e = t0 }
concrete : Pres.d inst (Pres.d inst (Pres.d inst (Pres.e inst))) ≡ Pres.e inst
concrete = refl
