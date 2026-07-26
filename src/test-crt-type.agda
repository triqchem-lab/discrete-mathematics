{-# OPTIONS --cubical --guardedness #-}

module test-crt-type where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _^_; _∸_)
open import Data.Nat using (_<_; _≤_)
open import Data.Nat.Properties using (≤-irrelevant)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using () renaming (_≡_ to _≡s_; refl to refls)

open import Cubical.Foundations.Prelude using (isProp→PathP; PathP; isProp)
open import Cubical.Foundations.Prelude using () renaming (_≡_ to _≡ᶜ_)
open import Cubical.Data.Sigma.Properties using (ΣPathP)

-- Bridge
≡s→≡c : ∀ {A : Set} {x y : A} → x ≡s y → x ≡ᶜ y
≡s→≡c refls = reflc
  where open import Cubical.Foundations.Prelude using () renaming (refl to reflc)

-- isProp for stdlib's ≤ (using Cubical's isProp notion)
isProp≤-stdlib : ∀ {m n : ℕ} → isProp (m ≤ n)
isProp≤-stdlib p q = ≡s→≡c (≤-irrelevant p q)

-- CRT domain types
M : ℕ ; M = 100
POW2 : ℕ ; POW2 = 10
POW3 : ℕ ; POW3 = 10

CRTDom : Set ; CRTDom = Σ ℕ (λ n → n < M)
CRTCod : Set ; CRTCod = (Σ ℕ (λ a → a < POW2)) × (Σ ℕ (λ b → b < POW3))

-- Postulate placeholder proofs (stand-in for actual arithmetic proofs)
postulate
  eq-a : ∀ a b → ((a + b) % M) % POW2 ≡s a
  eq-b : ∀ a b → ((a + b) % M) % POW3 ≡s b
  proof : ∀ n → (n % POW2 + n % POW3) % M ≡s n

-- Simulate crtProject'/crtReconstruct'
open import Data.Nat.DivMod using (m%n<n)

crtProject' : CRTDom → CRTCod
crtProject' (n , n<M) = (n % POW2 , m%n<n n POW2) , (n % POW3 , m%n<n n POW3)

crtReconstruct' : CRTCod → CRTDom
crtReconstruct' ((a , _) , (b , _)) = ((a + b) % M , m%n<n (a + b) M)

-- TEST 1: crtSec-restricted (the crucial pattern from CRT.agda)
test-crtSec : ∀ (p : CRTCod) → crtProject' (crtReconstruct' p) ≡ᶜ p
test-crtSec ((a , a<P2) , (b , b<P3)) =
  ΣPathP ( ΣPathP (≡s→≡c (eq-a a b) , isProp→PathP (λ _ → isProp≤-stdlib) _ _)
         , ΣPathP (≡s→≡c (eq-b a b) , isProp→PathP (λ _ → isProp≤-stdlib) _ _) )

-- TEST 2: crtRet-restricted (the other pattern from CRT.agda)
test-crtRet : ∀ (n : CRTDom) → crtReconstruct' (crtProject' n) ≡ᶜ n
test-crtRet (n , n<M) =
  ΣPathP ( ≡s→≡c (proof n)
         , isProp→PathP (λ _ → isProp≤-stdlib) _ _ )
