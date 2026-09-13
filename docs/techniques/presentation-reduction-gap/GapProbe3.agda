-- ③ **抽象实例**（生成元是 record 字段 = 展示群的抽象形态）：投影不归约 ⇒ REJECT
module GapProbe3 where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
record Pres : Set₁ where
  field
    A : Set
    d : A → A
    e : A
    d3 : ∀ x → d (d (d x)) ≡ x
abstract-instance : (p : Pres) → Pres.d p (Pres.d p (Pres.d p (Pres.e p))) ≡ Pres.e p
abstract-instance p = refl
