{-# OPTIONS --cubical --guardedness #-}

module Sovereign.Format.CRT where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _^_; _∸_)
open import Data.Nat.Properties using (*-comm; *-assoc; +-identityʳ; +-identityˡ; *-identityʳ; *-zeroʳ)
open import Data.Nat.DivMod using (%-distribˡ-+; %-distribˡ-*; m%n%n≡m%n)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Sovereign.Arithmetic.CRTLemmas using (coprime-POW2-POW3; crt-merge; POW2; POW3; M)

kT1 : ℕ ; kT1 = 24371
kT2 : ℕ ; kT2 = 111271
T1 : ℕ ; T1 = 4317249537
T2 : ℕ ; T2 = 7292256256

T1-proj1 : T1 % POW2 ≡ 1 ; T1-proj1 = refl
T1-proj2 : T1 % POW3 ≡ 0 ; T1-proj2 = refl
T2-proj1 : T2 % POW2 ≡ 0 ; T2-proj1 = refl
T2-proj2 : T2 % POW3 ≡ 1 ; T2-proj2 = refl
T1+T2-modM : (T1 + T2) % M ≡ 1 ; T1+T2-modM = refl

crtProject : ℕ → ℕ × ℕ ; crtProject x = (x % POW2 , x % POW3)
crtReconstruct : ℕ × ℕ → ℕ ; crtReconstruct (a , b) = (a * T1 + b * T2) % M

crtTheorem : ∀ (x : ℕ) → crtReconstruct (crtProject x) ≡ x % M
crtTheorem x = crt-merge (a * T1 + b * T2) x n%2≡x%2 n%3≡x%3
  where
    a = x % POW2 ; b = x % POW3 ; n = a * T1 + b * T2

    aT1%2 : (a * T1) % POW2 ≡ a % POW2
    aT1%2 = trans (%-distribˡ-* a T1 POW2)
             (trans (cong (λ u → ((a % POW2) * u) % POW2) T1-proj1)
             (trans (cong (_% POW2) (*-identityʳ (a % POW2)))
                    (m%n%n≡m%n a POW2)))

    bT2%2 : (b * T2) % POW2 ≡ 0
    bT2%2 = trans (%-distribˡ-* b T2 POW2)
             (trans (cong (λ u → ((b % POW2) * u) % POW2) T2-proj1)
             (trans (cong (_% POW2) (*-zeroʳ (b % POW2))) refl))

    n%2≡a%2 : n % POW2 ≡ a % POW2
    n%2≡a%2 = trans (%-distribˡ-+ (a * T1) (b * T2) POW2)
               (trans (cong₂ (λ u v → (u + v) % POW2) aT1%2 bT2%2)
               (trans (cong (_% POW2) (+-identityʳ (a % POW2)))
                      (m%n%n≡m%n a POW2)))

    n%2≡x%2 : n % POW2 ≡ x % POW2
    n%2≡x%2 = trans n%2≡a%2 (m%n%n≡m%n x POW2)

    aT1%3 : (a * T1) % POW3 ≡ 0
    aT1%3 = trans (%-distribˡ-* a T1 POW3)
             (trans (cong (λ u → ((a % POW3) * u) % POW3) T1-proj2)
             (trans (cong (_% POW3) (*-zeroʳ (a % POW3))) refl))

    bT2%3 : (b * T2) % POW3 ≡ b % POW3
    bT2%3 = trans (%-distribˡ-* b T2 POW3)
             (trans (cong (λ u → ((b % POW3) * u) % POW3) T2-proj2)
             (trans (cong (_% POW3) (*-identityʳ (b % POW3)))
                    (m%n%n≡m%n b POW3)))

    n%3≡b%3 : n % POW3 ≡ b % POW3
    n%3≡b%3 = trans (%-distribˡ-+ (a * T1) (b * T2) POW3)
               (trans (cong₂ (λ u v → (u + v) % POW3) aT1%3 bT2%3)
               (trans (cong (_% POW3) (+-identityˡ (b % POW3)))
                      (m%n%n≡m%n b POW3)))

    n%3≡x%3 : n % POW3 ≡ x % POW3
    n%3≡x%3 = trans n%3≡b%3 (m%n%n≡m%n x POW3)

CRT216 : ℕ ; CRT216 = 216
sqCongruence : (16 * 16) % CRT216 ≡ 40 % CRT216 ; sqCongruence = refl
divides216 : (16 * 16) ∸ 40 ≡ 216 ; divides216 = refl

data CRTEigenvalue : Set where
  e34 e0 e16⁺ e16⁻ : CRTEigenvalue

crtLabel : CRTEigenvalue → ℕ
crtLabel e34 = 34 ; crtLabel e0 = 0 ; crtLabel e16⁺ = 16 ; crtLabel e16⁻ = 16
e16-label-same : crtLabel e16⁺ ≡ crtLabel e16⁻ ; e16-label-same = refl
