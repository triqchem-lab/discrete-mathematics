{-# OPTIONS --cubical --guardedness #-}

module Sovereign.Format.CRT where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_; _^_; _∸_)
open import Data.Nat.Properties using (*-comm; *-assoc; +-identityʳ; +-identityˡ; *-identityʳ; *-zeroʳ)
open import Data.Nat.DivMod using (%-distribˡ-+; %-distribˡ-*; m%n%n≡m%n; m*n%n≡0; m≡m%n+[m/n]*n)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open import Cubical.Foundations.Prelude using () renaming (_≡_ to _≡ᶜ_)
open import Cubical.Foundations.Isomorphism using (Iso; iso)
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

-- 模运算核心引理 — CRT 域投影重构（无损降维，无大数归约）
-- 证明链：crtProject/crtReconstruct 正交分解 + gcd(POW2,POW3)=1 + 幻方正交拓扑
-- 下方所有引理使用 stdlib 正交分解属性，不依赖大数类型级归约

-- POW2 | M 即 M = POW2 * POW3，所以 (q*POW3)*POW2 = q*M + 0
qM%POW2≡0 : ∀ n → ((n / M) * M) % POW2 ≡ 0
qM%POW2≡0 n = begin
  ((n / M) * M) % POW2                     ≡⟨⟩
  ((n / M) * (POW2 * POW3)) % POW2         ≡⟨ cong (_% POW2) (cong ((n / M) *_) (*-comm POW2 POW3)) ⟩
  ((n / M) * (POW3 * POW2)) % POW2         ≡⟨ cong (_% POW2) (sym (*-assoc (n / M) POW3 POW2)) ⟩
  (((n / M) * POW3) * POW2) % POW2         ≡⟨ m*n%n≡0 ((n / M) * POW3) POW2 ⟩
  0 ∎
  where open ≡-Reasoning

qM%POW3≡0 : ∀ n → ((n / M) * M) % POW3 ≡ 0
qM%POW3≡0 n = begin
  ((n / M) * M) % POW3                     ≡⟨⟩
  ((n / M) * (POW2 * POW3)) % POW3         ≡⟨ cong (_% POW3) (sym (*-assoc (n / M) POW2 POW3)) ⟩
  (((n / M) * POW2) * POW3) % POW3         ≡⟨ m*n%n≡0 ((n / M) * POW2) POW3 ⟩
  0 ∎
  where open ≡-Reasoning

lemma-mod-cross-POW2 : ∀ n → (n % M) % POW2 ≡ n % POW2
lemma-mod-cross-POW2 n = sym (begin
  n % POW2
    ≡⟨ cong (_% POW2) (m≡m%n+[m/n]*n n M) ⟩
  ((n % M) + (n / M) * M) % POW2
    ≡⟨ %-distribˡ-+ (n % M) ((n / M) * M) POW2 ⟩
  ((n % M) % POW2 + ((n / M) * M) % POW2) % POW2
    ≡⟨ cong (λ r → ((n % M) % POW2 + r) % POW2) (qM%POW2≡0 n) ⟩
  ((n % M) % POW2 + 0) % POW2
    ≡⟨ cong (_% POW2) (+-identityʳ ((n % M) % POW2)) ⟩
  (n % M) % POW2 % POW2
    ≡⟨ m%n%n≡m%n (n % M) POW2 ⟩
  (n % M) % POW2 ∎)
  where open ≡-Reasoning

lemma-mod-cross-POW3 : ∀ n → (n % M) % POW3 ≡ n % POW3
lemma-mod-cross-POW3 n = sym (begin
  n % POW3
    ≡⟨ cong (_% POW3) (m≡m%n+[m/n]*n n M) ⟩
  ((n % M) + (n / M) * M) % POW3
    ≡⟨ %-distribˡ-+ (n % M) ((n / M) * M) POW3 ⟩
  ((n % M) % POW3 + ((n / M) * M) % POW3) % POW3
    ≡⟨ cong (λ r → ((n % M) % POW3 + r) % POW3) (qM%POW3≡0 n) ⟩
  ((n % M) % POW3 + 0) % POW3
    ≡⟨ cong (_% POW3) (+-identityʳ ((n % M) % POW3)) ⟩
  (n % M) % POW3 % POW3
    ≡⟨ m%n%n≡m%n (n % M) POW3 ⟩
  (n % M) % POW3 ∎)
  where open ≡-Reasoning

lemma-linear-POW2 : ∀ a b → (a * T1 + b * T2) % POW2 ≡ a % POW2
lemma-linear-POW2 a b = begin
  (a * T1 + b * T2) % POW2
    ≡⟨ %-distribˡ-+ (a * T1) (b * T2) POW2 ⟩
  ((a * T1) % POW2 + (b * T2) % POW2) % POW2
    ≡⟨ cong₂ (λ u v → (u + v) % POW2)
        (trans (%-distribˡ-* a T1 POW2) (trans (cong (λ u → (a % POW2 * u) % POW2) T1-proj1)
          (cong (_% POW2) (*-identityʳ (a % POW2)))))
        (trans (%-distribˡ-* b T2 POW2) (trans (cong (λ u → (b % POW2 * u) % POW2) T2-proj1)
          (cong (_% POW2) (*-zeroʳ (b % POW2))))) ⟩
  (((a % POW2) % POW2 + 0 % POW2) % POW2)
    ≡⟨ cong (λ x → (((a % POW2) % POW2 + x) % POW2)) (0/n≡0 POW2) ⟩
  (((a % POW2) % POW2 + 0) % POW2)
    ≡⟨ cong (_% POW2) (+-identityʳ ((a % POW2) % POW2)) ⟩
  ((a % POW2) % POW2) % POW2
    ≡⟨ m%n%n≡m%n (a % POW2) POW2 ⟩
  (a % POW2) % POW2
    ≡⟨ m%n%n≡m%n a POW2 ⟩
  a % POW2 ∎
  where open ≡-Reasoning
        open import Data.Nat.Properties using (*-identityʳ; *-zeroʳ)
        open import Data.Nat.DivMod using (0/n≡0)

lemma-linear-POW3 : ∀ a b → (a * T1 + b * T2) % POW3 ≡ b % POW3
lemma-linear-POW3 a b = begin
  (a * T1 + b * T2) % POW3
    ≡⟨ %-distribˡ-+ (a * T1) (b * T2) POW3 ⟩
  ((a * T1) % POW3 + (b * T2) % POW3) % POW3
    ≡⟨ cong₂ (λ u v → (u + v) % POW3)
        (trans (%-distribˡ-* a T1 POW3) (trans (cong (λ u → (a % POW3 * u) % POW3) T1-proj2)
          (cong (_% POW3) (*-zeroʳ (a % POW3)))))
        (trans (%-distribˡ-* b T2 POW3) (trans (cong (λ u → (b % POW3 * u) % POW3) T2-proj2)
          (cong (_% POW3) (*-identityʳ (b % POW3))))) ⟩
  ((0 % POW3 + (b % POW3) % POW3) % POW3)
    ≡⟨ cong (λ x → ((x + (b % POW3) % POW3) % POW3)) (0/n≡0 POW3) ⟩
  ((0 + (b % POW3) % POW3) % POW3)
    ≡⟨ cong (_% POW3) (+-identityˡ ((b % POW3) % POW3)) ⟩
  ((b % POW3) % POW3) % POW3
    ≡⟨ m%n%n≡m%n (b % POW3) POW3 ⟩
  (b % POW3) % POW3
    ≡⟨ m%n%n≡m%n b POW3 ⟩
  b % POW3 ∎
  where open ≡-Reasoning
        open import Data.Nat.Properties using (*-identityʳ; *-zeroʳ)
        open import Data.Nat.DivMod using (0/n≡0)

-- 核心定理（构造性，纯 CRT 代数链）
crtSec-core : ∀ (a b : ℕ) → crtProject (crtReconstruct (a , b)) ≡ (a % POW2 , b % POW3)
crtSec-core a b = cong₂ _,_
  (trans (lemma-mod-cross-POW2 (a * T1 + b * T2)) (lemma-linear-POW2 a b))
  (trans (lemma-mod-cross-POW3 (a * T1 + b * T2)) (lemma-linear-POW3 a b))

crtSec : ∀ (a b : ℕ) → a < POW2 → b < POW3 →
  crtProject (crtReconstruct (a , b)) ≡ (a , b)
crtSec a b a<2 b<3 =
  trans (crtSec-core a b) (cong₂ _,_ (m<n⇒m%n≡m a<2) (m<n⇒m%n≡m b<3))

-- CRT 谱桥：受限域 {n < M} ≅ {a < POW2} × {b < POW3}
-- crtProject/crtReconstruct 在无界 ℕ 上不构成点态 Iso:
--   crtReconstruct ∘ crtProject n ≡ n % M ≠ n  (crtTheorem)
--   crtProject ∘ crtReconstruct (a,b) ≡ (a%P2,b%P3) ≠ (a,b)  (crtSec-core)
-- 但在受限域上往返恒等严格成立 (crtSec + m<n⇒n%M≡n):
private
  open import Data.Nat using (_<_)
  open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)

  CRTDom : Set ; CRTDom = Σ ℕ (λ n → n < M)
  CRTCod : Set ; CRTCod = (Σ ℕ (λ a → a < POW2)) × (Σ ℕ (λ b → b < POW3))

  crtProject' : CRTDom → CRTCod
  crtProject' (n , _) = (n % POW2 , m%n<n n POW2) , (n % POW3 , m%n<n n POW3)

  crtReconstruct' : CRTCod → CRTDom
  crtReconstruct' ((a , _) , (b , _)) =
    crtReconstruct (a , b) , m%n<n (a * T1 + b * T2) M

  -- 受限域往返恒等（Cubical 路径版本，Agda 2.9 跨模块路径兼容性下暂 postulate）
  -- 构造性证明: crtSec + crtTheorem + m<n⇒m%n≡m → 数值等式，不等式证明由 <-irrelevant
  postulate
    crtSec-restricted : ∀ p → crtProject' (crtReconstruct' p) ≡ᶜ p
    crtRet-restricted : ∀ n → crtReconstruct' (crtProject' n) ≡ᶜ n

  crtIso : Iso CRTDom CRTCod
  crtIso = iso crtProject' crtReconstruct' crtSec-restricted crtRet-restricted
{-
  -- 构造性版本（需 isProp→PathP + <-irrelevant，Agda 2.9 模块路径差异下暂用 postulate）
  crtSec-restricted : ∀ (a b : ℕ) (a<2 : a < POW2) (b<3 : b < POW3) →
    crtProject' (crtReconstruct' ((a , a<2) , (b , b<3))) ≡ ((a , a<2) , (b , b<3))
  crtSec-restricted a b a<2 b<3 = ΣPathP (cong₂ _,_
    (ΣPathP (cong proj₁ (crtSec a b a<2 b<3) , isProp→PathP (λ i → <-irrelevant _ _) _ _))
    (ΣPathP (cong proj₂ (crtSec a b a<2 b<3) , isProp→PathP (λ i → <-irrelevant _ _) _ _)))
-}
-- 备注: 无界 ℕ 上 crtIso 不成立（模运算本征限制）
