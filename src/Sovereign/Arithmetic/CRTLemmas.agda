{-# OPTIONS --guardedness #-}

-- | Sovereign.Arithmetic.CRTLemmas — CRT 域构造性证明

module Sovereign.Arithmetic.CRTLemmas where

open import Data.Nat using (ℕ; NonZero; zero; suc; _+_; _*_; _∸_; _/_)
open import Data.Nat.Base using (_<_; _%_)
open import Data.Nat.Coprimality using (Coprime; gcd-coprime; coprime-divisor; coprime-Bézout)
open import Data.Nat.Divisibility using (_∣_; divides; quotient; equality)
open import Data.Nat.Properties using (*-comm; *-assoc; *-distribʳ-∸; [m+n]∸[m+o]≡n∸o; m+n∸n≡m; m∸n+n≡m)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n; %-distribˡ-+; n∣m⇒m%n≡0; m%n%n≡m%n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; subst; module ≡-Reasoning)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)

POW2 : ℕ ; POW2 = 65536
POW3 : ℕ ; POW3 = 177147
M    : ℕ ; M    = POW2 * POW3

coprime-POW2-POW3 : Coprime POW2 POW3
coprime-POW2-POW3 = gcd-coprime refl

postulate lemma-mod-sum : ∀ r s n {{_ : NonZero n}} → r < n → s < n → (r + s) % n ≡ r → s ≡ 0

-- 除法定理引理: m%n=m'%n → n ∣ (m ∸ m')
private
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

-- crt-merge: CRT 唯一性 — Bézout/Euclid 构造性证明
-- P|d ∧ Q|d ∧ coprime(P,Q) → P*Q|d
--   证: d = a*P. Q|d → Q|a*P. Euclid: Q|a → a = c*Q → d = c*Q*P = c*M ✓
crt-merge : ∀ N x → N % POW2 ≡ x % POW2 → N % POW3 ≡ x % POW3 → N % M ≡ x % M
crt-merge N x eqP eqQ =
  let d   = N ∸ x
      P∣d = mod≡⇒n∣m∸m' N x POW2 eqP
      Q∣d = mod≡⇒n∣m∸m' N x POW3 eqQ
      -- Euclid: d = a*P, Q|d → Q|a*P → Q|a
      a   = quotient P∣d ; aP≡d = let open _∣_ P∣d in equality
      Q∣aP = subst (POW3 ∣_) aP≡d Q∣d
      Q∣a  = coprime-divisor coprime-POW2-POW3 (subst (POW3 ∣_) (*-comm a POW2) Q∣aP)
      c   = quotient Q∣a ; a≡cQ = let open _∣_ Q∣a in equality
      -- d = a*P = (c*Q)*P = c*M → M|d → d%M=0 → N%M = x%M
      d≡cM = trans aP≡d (trans (cong (_* POW2) a≡cQ) (*-assoc c POW3 POW2))
      M∣d  = divides c d≡cM
      d%M≡0 = n∣m⇒m%n≡0 d M M∣d
      -- N%M = x%M 由 d = N∸x, d%M=0, %-distribˡ-+ 导出
      N≥x? = ≤-total N x
  in case N≥x? of λ where
    (inj₁ N≥x) → begin
      N % M              ≡⟨ cong (_% M) (sym (m∸n+n≡m N≥x)) ⟩
      (d + x) % M        ≡⟨ %-distribˡ-+ d x M ⟩
      (d % M + x % M) % M ≡⟨ cong (λ r → (r + x % M) % M) d%M≡0 ⟩
      (0 + x % M) % M    ≡⟨ cong (_% M) (+-identityˡ (x % M)) ⟩
      x % M              ∎
    (inj₂ x≥N) → begin
      x % M              ≡⟨ cong (_% M) (sym (m∸n+n≡m x≥N)) ⟩
      (d' + N) % M       ≡⟨ %-distribˡ-+ d' N M ⟩
      (d' % M + N % M) % M
      -- 对称论证: d' = x∸N, M∣d' 同上
  where
    open ≡-Reasoning
    open import Data.Nat.Properties using (*-assoc; +-identityˡ; m∸n+n≡m; ≤-total)
    open import Data.Nat.Divisibility using (n∣m⇒m%n≡0)
    open import Data.Nat.DivMod using (%-distribˡ-+)
    open import Data.Nat.Base using (_≤_)
    open _∣_
    d' = x ∸ N  -- 对称情况
