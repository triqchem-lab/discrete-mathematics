-- ① 具体生成的**闭合实例**：归一化器能算 ⇒ refl 可用（期望 ACCEPT）
module GapProbe1 where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import T3 using (T3; t0; step)
closed : step (step (step t0)) ≡ t0
closed = refl
