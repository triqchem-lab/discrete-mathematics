module _test_bases_proof where

open import Data.Nat using (ℕ)
open import Data.Nat.DivMod using (_%_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

LCM : ℕ
LCM = 11609505792

-- Agda 直接计算 8 % LCM。8 < LCM，所以 8 % LCM = 8。
-- 假设 8 % LCM ≡ 0，则 refl 给出 8 ≡ 0，矛盾（数字 8 ≠ 0）。

proof8  : 8  % LCM ≡ 0 → ⊥; proof8  ()
proof10 : 10 % LCM ≡ 0 → ⊥; proof10 ()
proof12 : 12 % LCM ≡ 0 → ⊥; proof12 ()
proof16 : 16 % LCM ≡ 0 → ⊥; proof16 ()
proof20 : 20 % LCM ≡ 0 → ⊥; proof20 ()
proof24 : 24 % LCM ≡ 0 → ⊥; proof24 ()
proof30 : 30 % LCM ≡ 0 → ⊥; proof30 ()
proof32 : 32 % LCM ≡ 0 → ⊥; proof32 ()
proof40 : 40 % LCM ≡ 0 → ⊥; proof40 ()
proof48 : 48 % LCM ≡ 0 → ⊥; proof48 ()
