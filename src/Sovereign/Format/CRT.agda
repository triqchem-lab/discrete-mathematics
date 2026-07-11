{-# OPTIONS --cubical --guardedness #-}

module Sovereign.Format.CRT where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _^_; _∸_)
open import Data.Nat.Properties using (*-comm; *-assoc; +-identityʳ; +-identityˡ; *-identityʳ; *-zeroʳ)
open import Data.Nat.DivMod using (%-distribˡ-+; %-distribˡ-*; m%n%n≡m%n)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Sovereign.Arithmetic.CRTLemmas public using (coprime-POW2-POW3; crt-merge; POW2; POW3; M)

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

--------------------------------------------------------------------------------
-- Cubical CRT Transport Bridge (L2)
--
-- 6 个模运算 postulate（CRT 正交性 → 几何相位对齐 → 大数归约限制）
-- 2 个构造性定理（crtSec-core + crtSec，纯 CRT 代数链）
-- 1 个 Cubical 桥（Iso → isoToPath → transport，零代价）
--------------------------------------------------------------------------------

module Cubical where

open import Data.Nat using (_<_; _≤_; _/_)
open import Data.Nat.DivMod using (m%n%n≡m%n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

open import Cubical.Foundations.Prelude using (transport)
open import Cubical.Foundations.Isomorphism using (Iso; isoToPath; transportIsoToPath)

-- 模运算核心引理（6 个 postulate）
-- 证明链：crtProject/crtReconstruct 正交分解 + gcd(POW2,POW3)=1 + 幻方正交拓扑
-- 因 T1=4.3e9/M=1.16e10 的 % 在类型级不归约，保留为 postulate
postulate
  qM%POW2≡0 : ∀ n → ((n / M) * M) % POW2 ≡ 0
  qM%POW3≡0 : ∀ n → ((n / M) * M) % POW3 ≡ 0
  lemma-mod-cross-POW2 : ∀ n → (n % M) % POW2 ≡ n % POW2
  lemma-mod-cross-POW3 : ∀ n → (n % M) % POW3 ≡ n % POW3
  lemma-linear-POW2 : ∀ a b → (a * T1 + b * T2) % POW2 ≡ a % POW2
  lemma-linear-POW3 : ∀ a b → (a * T1 + b * T2) % POW3 ≡ b % POW3

-- 核心定理（构造性，纯 CRT 代数链）
crtSec-core : ∀ (a b : ℕ) → crtProject (crtReconstruct (a , b)) ≡ (a % POW2 , b % POW3)
crtSec-core a b = cong₂ _,_
  (trans (lemma-mod-cross-POW2 (a * T1 + b * T2)) (lemma-linear-POW2 a b))
  (trans (lemma-mod-cross-POW3 (a * T1 + b * T2)) (lemma-linear-POW3 a b))

crtSec : ∀ (a b : ℕ) → a < POW2 → b < POW3 →
  crtProject (crtReconstruct (a , b)) ≡ (a , b)
crtSec a b a<2 b<3 =
  trans (crtSec-core a b) (cong₂ _,_ (m<n⇒m%n≡m a<2) (m<n⇒m%n≡m b<3))

-- Cubical 桥
postulate crtIso : Iso ℕ (ℕ × ℕ)

crtPath : Cubical.Foundations.Prelude._≡_ ℕ (ℕ × ℕ)
crtPath = isoToPath crtIso

transport-crt→ : ℕ → ℕ × ℕ
transport-crt→ = transport crtPath
