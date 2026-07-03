module _test_algebraic where
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Nat using (ℕ; _+_; _*_; _<_; zero)
open import Data.Nat.Base using (_%_) ; open import Data.Nat.DivMod using (_/_; [m+kn]%n≡m%n; m*n/n≡m)
open import Data.Nat.Properties using (m%n<n; m<n⇒m%n≡m; *-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

Trit = Fin 3

pack5 : Vec Trit 5 → ℕ
pack5 (a ∷ b ∷ c ∷ d ∷ e ∷ []) = toℕ a + toℕ b * 3 + toℕ c * 9 + toℕ d * 27 + toℕ e * 81

unpack5 : ℕ → Vec Trit 5
unpack5 n = (n mod 3) ∷ (n / 3 mod 3) ∷ (n / 9 mod 3) ∷ (n / 27 mod 3) ∷ (n / 81 mod 3) ∷ []

-- Key lemma: [m+kn]%n≡m%n
-- pack5 uses m = v0, k = v1+v2*3+v3*9+v4*27, n = 3
test1 : ∀ v0 v1 v2 v3 v4 → (toℕ v0 + (toℕ v1 * 3 + toℕ v2 * 9 + toℕ v3 * 27 + toℕ v4 * 81)) % 3 ≡ toℕ v0 % 3
test1 v0 v1 v2 v3 v4 = [m+kn]%n≡m%n (toℕ v0) (toℕ v1 + toℕ v2 * 3 + toℕ v3 * 9 + toℕ v4 * 27) 3
