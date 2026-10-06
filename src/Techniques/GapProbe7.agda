-- ⑦ 对照：Π 型 + refl 的惯用法本身可行吗（控制实验）
module Techniques.GapProbe7 where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Techniques.T3 using (T3)
idlaw : ∀ (x : T3) → x ≡ x
idlaw = λ x → refl
