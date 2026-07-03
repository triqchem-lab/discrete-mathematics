module _rt where
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Vec using (Vec; map; _∷_; [])
open import Data.Vec.Properties using (eval; eval-*3)
open import Data.Nat using (ℕ; _+_; _*_; _<_; zero; s≤s; z≤n) renaming (suc to ℕsuc)
open import Data.Nat.DivMod using (_div_; _mod_; _/_; _%_; m≡m%n+[m/n]*n; m/n<m)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

Trit : Set ; Trit = Fin 3
p3 : Vec ℕ 3 ; p3 = 1 ∷ 3 ∷ 9 ∷ []

stc : Vec Trit 3 → ℕ ; stc sec = eval (map toℕ sec) p3
cts : ℕ → Vec Trit 3 ; cts n = enc 3 n where
  enc : (k : ℕ) → ℕ → Vec Trit k
  enc zero _ = [] ; enc (ℕsuc k) num = (num mod 3) ∷ enc k (num div 3)

-- Prove: toℕ (n mod 3) ≡ n % 3
mod-toℕ : ∀ n → toℕ (n mod 3) ≡ n % 3
mod-toℕ n = refl

-- Roundtrip for 3 trits
rt : ∀ n → stc (cts n) ≡ n
rt 0 = refl ; rt 1 = refl ; rt 2 = refl
rt n@(ℕsuc (ℕsuc (ℕsuc _))) with n / 3 | n % 3 | m≡m%n+[m/n]*n n 3 | m/n<m n 3 (s≤s (s≤s z≤n))
... | q | r | eq | q<n with stc (cts q) | rt q
... | sq | ihq = 
  -- Goal: stc(cts n) ≡ n
  -- stc(cts n) = eval(map toℕ(enc 3 n)) p3 
  --            = eval(map toℕ((n mod 3) ∷ enc 2 q)) (1 ∷ 3 ∷ 9 ∷ [])
  --            = toℕ(n mod 3) + eval(map toℕ(enc 2 q)) (3 ∷ 9 ∷ [])
  -- 3 ∷ 9 ∷ [] = map (*3) (1 ∷ 3 ∷ []) = map (*3) (take 2 p3)
  -- eval-*3: = r + 3 * eval(map toℕ(enc 2 q)) (1 ∷ 3 ∷ [])
  -- lemma: eval(map toℕ(enc 2 q)) (1 ∷ 3 ∷ []) = stc(cts q) = sq
  -- by IH: sq = q
  -- = r + 3 * q = n (by Euclidean eq)
  trans (cong (r +_) (trans (eval-*3 (map toℕ (enc 2 q)) (1 ∷ 3 ∷ [])) 
        (cong (3 *_) {!!}))) eq
  where
  enc = cts.enc
