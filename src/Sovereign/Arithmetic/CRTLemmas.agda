{-# OPTIONS --guardedness #-}

module Sovereign.Arithmetic.CRTLemmas where

open import Data.Nat using (ℕ; NonZero; zero; suc; _+_; _*_; _∸_; _/_; _≤?_)
open import Data.Nat.GCD using (gcd)
open import Data.Nat.Base using (_<_; _%_; _≤_; NonZero; nonZero; >-nonZero; s≤s; z≤n)
open import Data.Nat.Coprimality using (Coprime; gcd≡1⇒coprime; coprime-divisor)
open import Data.Nat.Divisibility.Core using (_∣_; quotient)
open import Data.Nat.Divisibility using (n∣m⇒m%n≡0)
open import Data.Nat.Properties using (*-comm; *-assoc; *-distribʳ-∸; *-distribˡ-∸; [m+n]∸[m+o]≡n∸o; m+n∸n≡m; m∸n+n≡m; +-identityˡ; ≰⇒≥)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n; %-distribˡ-+; m%n%n≡m%n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (Dec; yes; no)

POW2 : ℕ ; POW2 = 65536
POW3 : ℕ ; POW3 = 177147
M    : ℕ ; M    = POW2 * POW3

coprime-POW2-POW3 : Coprime POW2 POW3
coprime-POW2-POW3 = gcd≡1⇒coprime refl

-- NonZero 实例: 65536 和 177147 显然 >0
instance
  POW2-nz : NonZero POW2 ; POW2-nz = nonZero
  POW3-nz : NonZero POW3 ; POW3-nz = nonZero
  M-nz    : NonZero M    ; M-nz    = nonZero

postulate lemma-mod-sum : ∀ r s n {{_ : NonZero n}} → r < n → s < n → (r + s) % n ≡ r → s ≡ 0

mod≡⇒n∣m∸m' : ∀ m m' n {{nz : NonZero n}} → m % n ≡ m' % n → n ∣ (m ∸ m')
mod≡⇒n∣m∸m' m m' n eq = record { quotient = q ∸ q' ; equality = pf }
  where
    r = m % n ; q = m / n ; q' = m' / n
    open ≡-Reasoning
    pf : m ∸ m' ≡ (q ∸ q') * n
    pf = trans step1 (trans step2 step3)
      where
        step1 : m ∸ m' ≡ (r + q * n) ∸ (r + q' * n)
        step1 = cong₂ _∸_ (m≡m%n+[m/n]*n m n)
                          (trans (m≡m%n+[m/n]*n m' n) (cong (λ x → x + m' / n * n) (sym eq)))
        step2 : (r + q * n) ∸ (r + q' * n) ≡ (q * n) ∸ (q' * n)
        step2 = [m+n]∸[m+o]≡n∸o r (q * n) (q' * n)
        step3 : (q * n) ∸ (q' * n) ≡ (q ∸ q') * n
        step3 = trans (cong₂ _∸_ (*-comm q n) (*-comm q' n))
                      (trans (sym (*-distribʳ-∸ n q q'))
                             (*-comm n (q ∸ q')))

euclid-%≡0 : ∀ m m' → m % POW2 ≡ m' % POW2 → m % POW3 ≡ m' % POW3 → (m ∸ m') % M ≡ 0
euclid-%≡0 m m' eP eQ =
  let d₀  = m ∸ m'
      P∣d₀ = mod≡⇒n∣m∸m' m m' POW2 eP
      Q∣d₀ = mod≡⇒n∣m∸m' m m' POW3 eQ
      a₀   = quotient P∣d₀ ; aP≡d₀ = _∣_.equality P∣d₀
      Q∣a₀P = subst (POW3 ∣_) aP≡d₀ Q∣d₀
      Q∣a₀  = coprime-divisor coprime-POW2-POW3 (subst (POW3 ∣_) (*-comm a₀ POW2) Q∣a₀P)
      c₀   = quotient Q∣a₀ ; a≡cQ₀ = _∣_.equality Q∣a₀
      d₀≡cM = trans aP≡d₀ (trans (cong (_* POW2) a≡cQ₀) (*-assoc c₀ POW3 POW2))
      M∣d₀  = record { quotient = c₀ ; equality = d₀≡cM }
  in n∣m⇒m%n≡0 d₀ M M∣d₀

-- crt-merge: CRT 唯一性 — Bézout/Euclid 构造性
crt-merge : ∀ N x → N % POW2 ≡ x % POW2 → N % POW3 ≡ x % POW3 → N % M ≡ x % M
crt-merge N x eP eQ = go (N ≤? x)
  where
    open ≡-Reasoning
    d  = N ∸ x ; d' = x ∸ N
    d%M≡0  = euclid-%≡0 N x eP eQ
    d'%M≡0 = euclid-%≡0 x N (sym eP) (sym eQ)
    go : Dec (N ≤ x) → N % M ≡ x % M
    go (yes N≤x) = begin
      x % M ≡⟨ cong (_% M) (sym (m∸n+n≡m N≤x)) ⟩
      (d' + N) % M ≡⟨ %-distribˡ-+ d' N M ⟩
      (d' % M + N % M) % M ≡⟨ cong (λ r → (r + N % M) % M) d'%M≡0 ⟩
      (0 + N % M) % M ≡⟨ cong (_% M) (+-identityˡ (N % M)) ⟩
      N % M ∎
    go (no  N≰x) = begin
      N % M ≡⟨ cong (_% M) (sym (m∸n+n≡m (≰⇒≥ N≰x))) ⟩
      (d + x) % M ≡⟨ %-distribˡ-+ d x M ⟩
      (d % M + x % M) % M ≡⟨ cong (λ r → (r + x % M) % M) d%M≡0 ⟩
      (0 + x % M) % M ≡⟨ cong (_% M) (+-identityˡ (x % M)) ⟩
      x % M ∎
