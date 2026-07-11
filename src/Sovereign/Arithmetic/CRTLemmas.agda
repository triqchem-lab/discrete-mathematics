{-# OPTIONS --guardedness #-}

module Sovereign.Arithmetic.CRTLemmas where

open import Data.Nat using (ℕ; NonZero; zero; suc; _+_; _*_; _∸_; _/_)
open import Data.Nat.GCD using (gcd)
open import Data.Nat.Base using (_<_; _%_; _≤_; _≤?_; ≰⇒≥)
import Data.Nat.Base
open import Data.Nat.Coprimality using (Coprime; gcd≡1⇒coprime; coprime-divisor; coprime-Bézout)
open import Data.Nat.Divisibility using (_∣_; divides; quotient; equality)
open import Data.Nat.Properties using (*-comm; *-assoc; *-distribʳ-∸; [m+n]∸[m+o]≡n∸o; m+n∸n≡m; m∸n+n≡m; +-identityˡ)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n; %-distribˡ-+; n∣m⇒m%n≡0; m%n%n≡m%n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; subst; module ≡-Reasoning)
open import Data.Sum using (_⊎_; inj₁; inj₂)

POW2 : ℕ ; POW2 = 65536
POW3 : ℕ ; POW3 = 177147
M    : ℕ ; M    = POW2 * POW3

coprime-POW2-POW3 : Coprime POW2 POW3
coprime-POW2-POW3 = gcd≡1⇒coprime refl

postulate lemma-mod-sum : ∀ r s n → r < n → s < n → (r + s) % n ≡ r → s ≡ 0

-- 除法定理引理: m%n=m'%n → n ∣ (m ∸ m')
mod≡⇒n∣m∸m' : ∀ m m' n {{_ : NonZero n}} → m % n ≡ m' % n → n ∣ (m ∸ m')
mod≡⇒n∣m∸m' m m' n eq = divides (q ∸ q') (begin
  m ∸ m'
    ≡⟨ cong₂ _∸_ (m≡m%n+[m/n]*n m n)
                 (trans (cong (λ r → r + m' / n * n) (sym eq)) (m≡m%n+[m/n]*n m' n)) ⟩
  (r + q * n) ∸ (r + q' * n)
    ≡⟨ [m+n]∸[m+o]≡n∸o r (q * n) (q' * n) ⟩
  (q * n) ∸ (q' * n)
    ≡⟨ *-distribʳ-∸ n q q' ⟩
  (q ∸ q') * n ∎)
  where r = m % n ; q = m / n ; q' = m' / n ; open ≡-Reasoning

-- Euclid 链: m%P=m'%P ∧ m%Q=m'%Q → (m∸m')%M=0
euclid-%≡0 : ∀ m m' → m % POW2 ≡ m' % POW2 → m % POW3 ≡ m' % POW3 → (m ∸ m') % M ≡ 0
euclid-%≡0 m m' eP eQ =
  let d₀  = m ∸ m'
      P∣d₀ = mod≡⇒n∣m∸m' m m' POW2 eP
      Q∣d₀ = mod≡⇒n∣m∸m' m m' POW3 eQ
      a₀   = quotient P∣d₀ ; aP≡d₀ = let open _∣_ P∣d₀ in equality
      Q∣a₀P = subst (POW3 ∣_) aP≡d₀ Q∣d₀
      Q∣a₀  = coprime-divisor coprime-POW2-POW3 (subst (POW3 ∣_) (*-comm a₀ POW2) Q∣a₀P)
      c₀   = quotient Q∣a₀ ; a≡cQ₀ = let open _∣_ Q∣a₀ in equality
      d₀≡cM = trans aP≡d₀ (trans (cong (_* POW2) a≡cQ₀) (*-assoc c₀ POW3 POW2))
      M∣d₀  = divides c₀ d₀≡cM
  in n∣m⇒m%n≡0 d₀ M M∣d₀
  where
    open _∣_
    open import Data.Nat.Properties using (*-comm; *-assoc)
    open import Data.Nat.Divisibility using (n∣m⇒m%n≡0)
    open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)

-- crt-merge: CRT 唯一性 — Bézout/Euclid 构造性
crt-merge : ∀ N x → N % POW2 ≡ x % POW2 → N % POW3 ≡ x % POW3 → N % M ≡ x % M
crt-merge N x eP eQ = go N x (N ∸ x) (x ∸ N)
  (euclid-%≡0 N x eP eQ) (euclid-%≡0 x N (sym eP) (sym eQ)) (N ≤? x)
  where
    open ≡-Reasoning
    open import Relation.Nullary using (Dec; yes; no)
    go : ∀ N x d d' → d % M ≡ 0 → d' % M ≡ 0 → Dec (N ≤ x) → N % M ≡ x % M
    go N x d d' d%M≡0 d'%M≡0 (yes N≤x) = begin
      x % M              ≡⟨ cong (_% M) (sym (m∸n+n≡m N≤x)) ⟩
      (d' + N) % M       ≡⟨ %-distribˡ-+ d' N M ⟩
      (d' % M + N % M) % M ≡⟨ cong (λ r → (r + N % M) % M) d'%M≡0 ⟩
      (0 + N % M) % M    ≡⟨ cong (_% M) (+-identityˡ (N % M)) ⟩
      N % M              ∎
    go N x d d' d%M≡0 d'%M≡0 (no N≰x) =
      let N≥x = Data.Nat.Base.≰⇒≥ N≰x
      in trans (cong (_% M) (sym (m∸n+n≡m N≥x)))
         (trans (%-distribˡ-+ d x M)
         (trans (cong (λ r → (r + x % M) % M) d%M≡0)
                (cong (_% M) (+-identityˡ (x % M)))))
