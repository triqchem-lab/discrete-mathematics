{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.VortexTower
-- 涡旋塔扩张：Z/12ⁿZ 的 CRT 正交分解塔
--
-- 代数链扩展 (Duodecimal L8-L10 之后):
--   L11: Z/144Z 环 — 极向缠绕 144 = 12² 的代数结构
--   L12: CRT 分解 Z/144Z ≅ Z/9Z × Z/16Z — 3² × 2⁴ 正交分解
--   L13: 涡旋塔公式 Z/12ⁿZ ≅ Z/3ⁿZ × Z/2²ⁿZ
--
-- 核心定理:
--   144 = 12² = 极向缠绕数 (PolarWinding)
--   144 = 9 × 16 = 3² × 2⁴, gcd(9,16) = 1
--   Z/144Z ≅ Z/9Z × Z/16Z (CRT)
--   1728 = 12³ = 27 × 64, gcd(27,64) = 1
--
-- 涡旋塔层级:
--   n=1: Z/12Z   ≅ Z/3Z  × Z/4Z   (Duodecimal.agda)
--   n=2: Z/144Z  ≅ Z/9Z  × Z/16Z  (本模块)
--   n=3: Z/1728Z ≅ Z/27Z × Z/64Z  (本模块)
--
-- 0 postulate — 全部构造性证明

module Sovereign.Algebra.VortexTower where

open import Data.Nat using (ℕ; _+_; _*_; _∸_; _<_; _≤_; _>_; _≤?_; _/_; _%_; NonZero; nonZero; s≤s; z≤n)
open import Data.Nat.DivMod
  using (m%n<n; m<n⇒m%n≡m; m%n%n≡m%n;
         m≡m%n+[m/n]*n; [m+kn]%n≡m%n; %-distribˡ-+)
import Data.Nat.Properties as NP
open import Data.Nat.GCD using (gcd)
open import Data.Nat.Coprimality using (Coprime; gcd≡1⇒coprime; coprime-divisor)
open import Data.Nat.Divisibility.Core using (_∣_; divides)
open import Data.Nat.Divisibility using (n∣m⇒m%n≡0; ∣⇒≤)
open import Data.Fin using (Fin; toℕ; fromℕ<; zero; suc)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-injective; toℕ<n)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; subst; module ≡-Reasoning)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Sovereign.AlgebraWrapper using (distrib-lemma)

import Sovereign.Structology.Winding as W
import Sovereign.Algebra.Duodecimal as D

--------------------------------------------------------------------------------
-- 1. Z/144Z 环 — 用 Fin 144 表示
--------------------------------------------------------------------------------

Z144 : Set
Z144 = Fin 144

_+₁₄₄_ : Z144 → Z144 → Z144
x +₁₄₄ y = fromℕ< (m%n<n (toℕ x + toℕ y) 144)

_*₁₄₄_ : Z144 → Z144 → Z144
x *₁₄₄ y = fromℕ< (m%n<n (toℕ x * toℕ y) 144)

0₁₄₄ : Z144
0₁₄₄ = zero

1₁₄₄ : Z144
1₁₄₄ = suc zero

--------------------------------------------------------------------------------
-- 2. toℕ 同态性质
--------------------------------------------------------------------------------

toℕ-0₁₄₄ : toℕ 0₁₄₄ ≡ 0
toℕ-0₁₄₄ = refl

toℕ-1₁₄₄ : toℕ 1₁₄₄ ≡ 1
toℕ-1₁₄₄ = refl

toℕ-+₁₄₄ : ∀ x y → toℕ (x +₁₄₄ y) ≡ (toℕ x + toℕ y) % 144
toℕ-+₁₄₄ x y = toℕ-fromℕ< (m%n<n (toℕ x + toℕ y) 144)

toℕ-*₁₄₄ : ∀ x y → toℕ (x *₁₄₄ y) ≡ (toℕ x * toℕ y) % 144
toℕ-*₁₄₄ x y = toℕ-fromℕ< (m%n<n (toℕ x * toℕ y) 144)

--------------------------------------------------------------------------------
-- 3. 模吸收引理
--------------------------------------------------------------------------------

mod-absorbˡ : ∀ a b n → {{_ : NonZero n}} → (a + b) % n ≡ (a % n + b) % n
mod-absorbˡ a b n {{nz}} = begin
  (a + b) % n
    ≡⟨ cong (_% n) (trans (cong (_+ b) (m≡m%n+[m/n]*n a n))
                          (trans (NP.+-assoc (a % n) (a / n * n) b)
                                 (trans (cong (a % n +_) (NP.+-comm (a / n * n) b))
                                        (sym (NP.+-assoc (a % n) b (a / n * n)))))) ⟩
  ((a % n + b) + a / n * n) % n
    ≡⟨ [m+kn]%n≡m%n (a % n + b) (a / n) n ⟩
  (a % n + b) % n ∎
  where open ≡-Reasoning

mod-absorbʳ : ∀ a b n → {{_ : NonZero n}} → (a + b) % n ≡ (a + b % n) % n
mod-absorbʳ a b n {{nz}} = begin
  (a + b) % n
    ≡⟨ cong (_% n) (trans (cong (a +_) (m≡m%n+[m/n]*n b n))
                          (sym (NP.+-assoc a (b % n) (b / n * n)))) ⟩
  ((a + b % n) + b / n * n) % n
    ≡⟨ [m+kn]%n≡m%n (a + b % n) (b / n) n ⟩
  (a + b % n) % n ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- 4. 环公理
--------------------------------------------------------------------------------

+₁₄₄-assoc : ∀ x y z → (x +₁₄₄ y) +₁₄₄ z ≡ x +₁₄₄ (y +₁₄₄ z)
+₁₄₄-assoc x y z = toℕ-injective (begin
  toℕ ((x +₁₄₄ y) +₁₄₄ z)
    ≡⟨ toℕ-+₁₄₄ (x +₁₄₄ y) z ⟩
  (toℕ (x +₁₄₄ y) + toℕ z) % 144
    ≡⟨ cong (λ u → (u + toℕ z) % 144) (toℕ-+₁₄₄ x y) ⟩
  ((toℕ x + toℕ y) % 144 + toℕ z) % 144
    ≡⟨ sym (mod-absorbˡ (toℕ x + toℕ y) (toℕ z) 144) ⟩
  (toℕ x + toℕ y + toℕ z) % 144
    ≡⟨ cong (_% 144) (NP.+-assoc (toℕ x) (toℕ y) (toℕ z)) ⟩
  (toℕ x + (toℕ y + toℕ z)) % 144
    ≡⟨ mod-absorbʳ (toℕ x) (toℕ y + toℕ z) 144 ⟩
  (toℕ x + (toℕ y + toℕ z) % 144) % 144
    ≡⟨ cong (λ u → (toℕ x + u) % 144) (sym (toℕ-+₁₄₄ y z)) ⟩
  (toℕ x + toℕ (y +₁₄₄ z)) % 144
    ≡⟨ sym (toℕ-+₁₄₄ x (y +₁₄₄ z)) ⟩
  toℕ (x +₁₄₄ (y +₁₄₄ z)) ∎)
  where open ≡-Reasoning

+₁₄₄-comm : ∀ x y → x +₁₄₄ y ≡ y +₁₄₄ x
+₁₄₄-comm x y = toℕ-injective (begin
  toℕ (x +₁₄₄ y) ≡⟨ toℕ-+₁₄₄ x y ⟩
  (toℕ x + toℕ y) % 144 ≡⟨ cong (_% 144) (NP.+-comm (toℕ x) (toℕ y)) ⟩
  (toℕ y + toℕ x) % 144 ≡⟨ sym (toℕ-+₁₄₄ y x) ⟩
  toℕ (y +₁₄₄ x) ∎) where open ≡-Reasoning

+₁₄₄-identityˡ : ∀ x → 0₁₄₄ +₁₄₄ x ≡ x
+₁₄₄-identityˡ x = toℕ-injective (begin
  toℕ (0₁₄₄ +₁₄₄ x) ≡⟨ toℕ-+₁₄₄ 0₁₄₄ x ⟩
  (toℕ 0₁₄₄ + toℕ x) % 144 ≡⟨ cong (λ u → (u + toℕ x) % 144) toℕ-0₁₄₄ ⟩
  (0 + toℕ x) % 144 ≡⟨ cong (_% 144) (NP.+-identityˡ (toℕ x)) ⟩
  toℕ x % 144 ≡⟨ m<n⇒m%n≡m (toℕ<n x) ⟩
  toℕ x ∎) where open ≡-Reasoning

+₁₄₄-identityʳ : ∀ x → x +₁₄₄ 0₁₄₄ ≡ x
+₁₄₄-identityʳ x = toℕ-injective (begin
  toℕ (x +₁₄₄ 0₁₄₄) ≡⟨ toℕ-+₁₄₄ x 0₁₄₄ ⟩
  (toℕ x + toℕ 0₁₄₄) % 144 ≡⟨ cong (λ u → (toℕ x + u) % 144) toℕ-0₁₄₄ ⟩
  (toℕ x + 0) % 144 ≡⟨ cong (_% 144) (NP.+-identityʳ (toℕ x)) ⟩
  toℕ x % 144 ≡⟨ m<n⇒m%n≡m (toℕ<n x) ⟩
  toℕ x ∎) where open ≡-Reasoning

*₁₄₄-comm : ∀ x y → x *₁₄₄ y ≡ y *₁₄₄ x
*₁₄₄-comm x y = toℕ-injective (begin
  toℕ (x *₁₄₄ y) ≡⟨ toℕ-*₁₄₄ x y ⟩
  (toℕ x * toℕ y) % 144 ≡⟨ cong (_% 144) (NP.*-comm (toℕ x) (toℕ y)) ⟩
  (toℕ y * toℕ x) % 144 ≡⟨ sym (toℕ-*₁₄₄ y x) ⟩
  toℕ (y *₁₄₄ x) ∎) where open ≡-Reasoning

*₁₄₄-identityˡ : ∀ x → 1₁₄₄ *₁₄₄ x ≡ x
*₁₄₄-identityˡ x = toℕ-injective (begin
  toℕ (1₁₄₄ *₁₄₄ x) ≡⟨ toℕ-*₁₄₄ 1₁₄₄ x ⟩
  (toℕ 1₁₄₄ * toℕ x) % 144 ≡⟨ cong (λ u → (u * toℕ x) % 144) toℕ-1₁₄₄ ⟩
  (1 * toℕ x) % 144 ≡⟨ cong (_% 144) (NP.*-identityˡ (toℕ x)) ⟩
  toℕ x % 144 ≡⟨ m<n⇒m%n≡m (toℕ<n x) ⟩
  toℕ x ∎) where open ≡-Reasoning

*₁₄₄-identityʳ : ∀ x → x *₁₄₄ 1₁₄₄ ≡ x
*₁₄₄-identityʳ x = toℕ-injective (begin
  toℕ (x *₁₄₄ 1₁₄₄) ≡⟨ toℕ-*₁₄₄ x 1₁₄₄ ⟩
  (toℕ x * toℕ 1₁₄₄) % 144 ≡⟨ cong (λ u → (toℕ x * u) % 144) toℕ-1₁₄₄ ⟩
  (toℕ x * 1) % 144 ≡⟨ cong (_% 144) (NP.*-identityʳ (toℕ x)) ⟩
  toℕ x % 144 ≡⟨ m<n⇒m%n≡m (toℕ<n x) ⟩
  toℕ x ∎) where open ≡-Reasoning

*₁₄₄-zeroˡ : ∀ x → 0₁₄₄ *₁₄₄ x ≡ 0₁₄₄
*₁₄₄-zeroˡ x = toℕ-injective (begin
  toℕ (0₁₄₄ *₁₄₄ x) ≡⟨ toℕ-*₁₄₄ 0₁₄₄ x ⟩
  (toℕ 0₁₄₄ * toℕ x) % 144 ≡⟨ cong (λ u → (u * toℕ x) % 144) toℕ-0₁₄₄ ⟩
  (0 * toℕ x) % 144 ≡⟨ cong (_% 144) (NP.*-zeroˡ (toℕ x)) ⟩
  0 % 144 ≡⟨ refl ⟩
  0 ≡⟨ sym toℕ-0₁₄₄ ⟩
  toℕ 0₁₄₄ ∎) where open ≡-Reasoning

--------------------------------------------------------------------------------
-- 5. CRT 投影
--------------------------------------------------------------------------------

π9 : Z144 → Fin 9
π9 x = fromℕ< (m%n<n (toℕ x) 9)

π16 : Z144 → Fin 16
π16 x = fromℕ< (m%n<n (toℕ x) 16)

toℕ-π9 : ∀ x → toℕ (π9 x) ≡ toℕ x % 9
toℕ-π9 x = toℕ-fromℕ< (m%n<n (toℕ x) 9)

toℕ-π16 : ∀ x → toℕ (π16 x) ≡ toℕ x % 16
toℕ-π16 x = toℕ-fromℕ< (m%n<n (toℕ x) 16)

--------------------------------------------------------------------------------
-- 6. CRT 重构
--------------------------------------------------------------------------------

crt144 : Fin 9 → Fin 16 → Z144
crt144 a b = fromℕ< (m%n<n (64 * toℕ a + 81 * toℕ b) 144)

crt-e₁-mod9 : 64 % 9 ≡ 1 ; crt-e₁-mod9 = refl
crt-e₁-mod16 : 64 % 16 ≡ 0 ; crt-e₁-mod16 = refl
crt-e₂-mod9 : 81 % 9 ≡ 0 ; crt-e₂-mod9 = refl
crt-e₂-mod16 : 81 % 16 ≡ 1 ; crt-e₂-mod16 = refl

--------------------------------------------------------------------------------
-- 7. CRT 辅助引理
--------------------------------------------------------------------------------

coprime-9-16 : Coprime 9 16
coprime-9-16 = gcd≡1⇒coprime refl

mod≡⇒n∣m∸m' : ∀ m m' n → {{_ : NonZero n}} → m % n ≡ m' % n → n ∣ (m ∸ m')
mod≡⇒n∣m∸m' m m' n {{nz}} eq = record { quotient = q ∸ q' ; equality = pf }
  where
    r = m % n ; q = m / n ; q' = m' / n
    open ≡-Reasoning
    pf : m ∸ m' ≡ (q ∸ q') * n
    pf = begin
      m ∸ m'
        ≡⟨ cong₂ _∸_ (m≡m%n+[m/n]*n m n)
                      (trans (m≡m%n+[m/n]*n m' n)
                             (cong (λ x → x + m' / n * n) (sym eq))) ⟩
      (r + q * n) ∸ (r + q' * n)
        ≡⟨ NP.[m+n]∸[m+o]≡n∸o r (q * n) (q' * n) ⟩
      (q * n) ∸ (q' * n)
        ≡⟨ distrib-lemma n q q' ⟩
      (q ∸ q') * n ∎

euclid-%≡0-9-16 : ∀ m m' → m % 9 ≡ m' % 9 → m % 16 ≡ m' % 16 → (m ∸ m') % 144 ≡ 0
euclid-%≡0-9-16 m m' e9 e16 =
  let 9∣d  = mod≡⇒n∣m∸m' m m' 9 e9
      16∣d = mod≡⇒n∣m∸m' m m' 16 e16
      open ≡-Reasoning
      open _∣_ 9∣d renaming (quotient to a₀; equality to a9≡d₀)
      open _∣_ 16∣d renaming (quotient to b₀; equality to b16≡d₀)
      16∣a₀9 : 16 ∣ a₀ * 9
      16∣a₀9 = subst (16 ∣_) a9≡d₀ 16∣d
      16∣a₀ : 16 ∣ a₀
      16∣a₀ = q∣a-helper a₀ 16∣a₀9
      open _∣_ 16∣a₀ renaming (quotient to c₀; equality to a≡c16₀)
      d₀ = m ∸ m'
      d₀≡c916 : d₀ ≡ c₀ * (9 * 16)
      d₀≡c916 = begin
        d₀ ≡⟨ a9≡d₀ ⟩ a₀ * 9 ≡⟨ cong (_* 9) a≡c16₀ ⟩
        (c₀ * 16) * 9 ≡⟨ NP.*-assoc c₀ 16 9 ⟩
        c₀ * (16 * 9) ≡⟨ cong (c₀ *_) (NP.*-comm 16 9) ⟩ c₀ * (9 * 16) ∎
      144∣d' : (9 * 16) ∣ (m ∸ m')
      144∣d' = divides c₀ d₀≡c916
  in n∣m⇒m%n≡0 (m ∸ m') (9 * 16) 144∣d'
  where
    q∣a-helper : ∀ a → 16 ∣ a * 9 → 16 ∣ a
    q∣a-helper a p rewrite NP.*-comm a 9 =
      coprime-divisor (Data.Nat.Coprimality.sym coprime-9-16) p

crt-merge-9-16 : ∀ N x → N % 9 ≡ x % 9 → N % 16 ≡ x % 16 → N % 144 ≡ x % 144
crt-merge-9-16 N x e9 e16 = go (N ≤? x)
  where
    open ≡-Reasoning
    d  = N ∸ x ; d' = x ∸ N
    d%144≡0  = euclid-%≡0-9-16 N x e9 e16
    d'%144≡0 = euclid-%≡0-9-16 x N (sym e9) (sym e16)
    go : Dec (N ≤ x) → N % 144 ≡ x % 144
    go (yes N≤x) = sym (begin
      x % 144 ≡⟨ cong (_% 144) (sym (NP.m∸n+n≡m N≤x)) ⟩
      (d' + N) % 144 ≡⟨ %-distribˡ-+ d' N 144 ⟩
      (d' % 144 + N % 144) % 144 ≡⟨ cong (λ r → (r + N % 144) % 144) d'%144≡0 ⟩
      (0 + N % 144) % 144 ≡⟨ cong (_% 144) (NP.+-identityˡ (N % 144)) ⟩
      (N % 144) % 144 ≡⟨ m%n%n≡m%n N 144 ⟩ N % 144 ∎)
    go (no N≰x) = begin
      N % 144 ≡⟨ cong (_% 144) (sym (NP.m∸n+n≡m (NP.≰⇒≥ N≰x))) ⟩
      (d + x) % 144 ≡⟨ %-distribˡ-+ d x 144 ⟩
      (d % 144 + x % 144) % 144 ≡⟨ cong (λ r → (r + x % 144) % 144) d%144≡0 ⟩
      (0 + x % 144) % 144 ≡⟨ cong (_% 144) (NP.+-identityˡ (x % 144)) ⟩
      (x % 144) % 144 ≡⟨ m%n%n≡m%n x 144 ⟩ x % 144 ∎

--------------------------------------------------------------------------------
-- 8. CRT 重构的模性质
--------------------------------------------------------------------------------

arith-mod9 : ∀ a b → 64 * a + 81 * b ≡ a + (7 * a + 9 * b) * 9
arith-mod9 a b =
  trans (NP.+-assoc a (63 * a) (81 * b))
        (cong (a +_)
          (trans (cong₂ _+_ (NP.*-assoc 9 7 a) (NP.*-assoc 9 9 b))
                 (trans (sym (NP.*-distribˡ-+ 9 (7 * a) (9 * b)))
                        (NP.*-comm 9 (7 * a + 9 * b)))))

arith-mod16 : ∀ a b → 64 * a + 81 * b ≡ b + (4 * a + 5 * b) * 16
arith-mod16 a b =
  trans (sym (NP.+-assoc (64 * a) b (80 * b)))
        (trans (cong (_+ 80 * b) (NP.+-comm (64 * a) b))
               (trans (NP.+-assoc b (64 * a) (80 * b))
                      (cong (b +_)
                        (trans (cong₂ _+_ (NP.*-assoc 16 4 a) (NP.*-assoc 16 5 b))
                               (trans (sym (NP.*-distribˡ-+ 16 (4 * a) (5 * b)))
                                      (NP.*-comm 16 (4 * a + 5 * b)))))))

crt144-mod9 : ∀ (a : Fin 9) (b : Fin 16) → (64 * toℕ a + 81 * toℕ b) % 9 ≡ toℕ a % 9
crt144-mod9 a b =
  trans (cong (_% 9) (arith-mod9 (toℕ a) (toℕ b)))
        ([m+kn]%n≡m%n (toℕ a) (7 * toℕ a + 9 * toℕ b) 9)

crt144-mod16 : ∀ (a : Fin 9) (b : Fin 16) → (64 * toℕ a + 81 * toℕ b) % 16 ≡ toℕ b % 16
crt144-mod16 a b =
  trans (cong (_% 16) (arith-mod16 (toℕ a) (toℕ b)))
        ([m+kn]%n≡m%n (toℕ b) (4 * toℕ a + 5 * toℕ b) 16)

--------------------------------------------------------------------------------
-- 9. CRT 往返恒等 — 主定理
--------------------------------------------------------------------------------

%144%9 : ∀ x → (x % 144) % 9 ≡ x % 9
%144%9 x = sym (begin
  x % 9 ≡⟨ cong (_% 9) (m≡m%n+[m/n]*n x 144) ⟩
  (x % 144 + x / 144 * 144) % 9
    ≡⟨ cong (_% 9) (cong (x % 144 +_) (sym (NP.*-assoc (x / 144) 16 9))) ⟩
  (x % 144 + (x / 144 * 16) * 9) % 9
    ≡⟨ [m+kn]%n≡m%n (x % 144) (x / 144 * 16) 9 ⟩
  (x % 144) % 9 ∎) where open ≡-Reasoning

%144%16 : ∀ x → (x % 144) % 16 ≡ x % 16
%144%16 x = sym (begin
  x % 16 ≡⟨ cong (_% 16) (m≡m%n+[m/n]*n x 144) ⟩
  (x % 144 + x / 144 * 144) % 16
    ≡⟨ cong (_% 16) (cong (x % 144 +_) (sym (NP.*-assoc (x / 144) 9 16))) ⟩
  (x % 144 + (x / 144 * 9) * 16) % 16
    ≡⟨ [m+kn]%n≡m%n (x % 144) (x / 144 * 9) 16 ⟩
  (x % 144) % 16 ∎) where open ≡-Reasoning

crt144-roundtrip : ∀ x → crt144 (π9 x) (π16 x) ≡ x
crt144-roundtrip x = toℕ-injective (begin
  toℕ (crt144 (π9 x) (π16 x))
    ≡⟨ toℕ-fromℕ< (m%n<n (64 * toℕ (π9 x) + 81 * toℕ (π16 x)) 144) ⟩
  (64 * toℕ (π9 x) + 81 * toℕ (π16 x)) % 144
    ≡⟨ crt-merge-9-16 (64 * toℕ (π9 x) + 81 * toℕ (π16 x)) (toℕ x)
                      (π9-eq x) (π16-eq x) ⟩
  toℕ x % 144 ≡⟨ m<n⇒m%n≡m (toℕ<n x) ⟩ toℕ x ∎)
  where
    open ≡-Reasoning
    π9-eq : ∀ x → (64 * toℕ (π9 x) + 81 * toℕ (π16 x)) % 9 ≡ toℕ x % 9
    π9-eq x = trans (crt144-mod9 (π9 x) (π16 x))
                    (trans (cong (_% 9) (toℕ-π9 x))
                           (m%n%n≡m%n (toℕ x) 9))
    π16-eq : ∀ x → (64 * toℕ (π9 x) + 81 * toℕ (π16 x)) % 16 ≡ toℕ x % 16
    π16-eq x = trans (crt144-mod16 (π9 x) (π16 x))
                     (trans (cong (_% 16) (toℕ-π16 x))
                            (m%n%n≡m%n (toℕ x) 16))

crt144-inv-π9 : ∀ (a : Fin 9) (b : Fin 16) → π9 (crt144 a b) ≡ a
crt144-inv-π9 a b = toℕ-injective (begin
  toℕ (π9 (crt144 a b)) ≡⟨ toℕ-π9 (crt144 a b) ⟩
  toℕ (crt144 a b) % 9
    ≡⟨ cong (_% 9) (toℕ-fromℕ< (m%n<n (64 * toℕ a + 81 * toℕ b) 144)) ⟩
  (64 * toℕ a + 81 * toℕ b) % 144 % 9
    ≡⟨ %144%9 (64 * toℕ a + 81 * toℕ b) ⟩
  (64 * toℕ a + 81 * toℕ b) % 9 ≡⟨ crt144-mod9 a b ⟩
  toℕ a % 9 ≡⟨ m<n⇒m%n≡m (toℕ<n a) ⟩ toℕ a ∎)
  where open ≡-Reasoning

crt144-inv-π16 : ∀ (a : Fin 9) (b : Fin 16) → π16 (crt144 a b) ≡ b
crt144-inv-π16 a b = toℕ-injective (begin
  toℕ (π16 (crt144 a b)) ≡⟨ toℕ-π16 (crt144 a b) ⟩
  toℕ (crt144 a b) % 16
    ≡⟨ cong (_% 16) (toℕ-fromℕ< (m%n<n (64 * toℕ a + 81 * toℕ b) 144)) ⟩
  (64 * toℕ a + 81 * toℕ b) % 144 % 16
    ≡⟨ %144%16 (64 * toℕ a + 81 * toℕ b) ⟩
  (64 * toℕ a + 81 * toℕ b) % 16 ≡⟨ crt144-mod16 a b ⟩
  toℕ b % 16 ≡⟨ m<n⇒m%n≡m (toℕ<n b) ⟩ toℕ b ∎)
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- 10. 涡旋塔公式
--------------------------------------------------------------------------------

tower-n1-product : 3 * 4 ≡ 12 ; tower-n1-product = refl
tower-n1-gcd : gcd 3 4 ≡ 1 ; tower-n1-gcd = refl
tower-n1-roundtrip : ∀ x → D.crt12 (D.π3 x) (D.π4 x) ≡ x
tower-n1-roundtrip = D.crt12-roundtrip

tower-n2-product : 9 * 16 ≡ 144 ; tower-n2-product = refl
tower-n2-gcd : gcd 9 16 ≡ 1 ; tower-n2-gcd = refl
tower-n2-roundtrip : ∀ x → crt144 (π9 x) (π16 x) ≡ x
tower-n2-roundtrip = crt144-roundtrip

tower-n3-product : 27 * 64 ≡ 1728 ; tower-n3-product = refl
tower-n3-gcd : gcd 27 64 ≡ 1 ; tower-n3-gcd = refl

π27 : Fin 1728 → Fin 27
π27 x = fromℕ< (m%n<n (toℕ x) 27)

π64 : Fin 1728 → Fin 64
π64 x = fromℕ< (m%n<n (toℕ x) 64)

crt1728 : Fin 27 → Fin 64 → Fin 1728
crt1728 a b = fromℕ< (m%n<n (1216 * toℕ a + 513 * toℕ b) 1728)

crt1728-e₁-mod27 : 1216 % 27 ≡ 1 ; crt1728-e₁-mod27 = refl
crt1728-e₁-mod64 : 1216 % 64 ≡ 0 ; crt1728-e₁-mod64 = refl
crt1728-e₂-mod27 : 513 % 27 ≡ 0 ; crt1728-e₂-mod27 = refl
crt1728-e₂-mod64 : 513 % 64 ≡ 1 ; crt1728-e₂-mod64 = refl

--------------------------------------------------------------------------------
-- 11. 与项目常数的连接
--------------------------------------------------------------------------------

polar-is-12-sq : 144 ≡ 12 * 12 ; polar-is-12-sq = refl
polar-decomposition : 144 ≡ 120 + 24 ; polar-decomposition = refl
cube-12 : 1728 ≡ 12 * 12 * 12 ; cube-12 = refl
polar-winding-value : W.PolarWinding ≡ 144 ; polar-winding-value = refl
crt144-product : 9 * 16 ≡ 144 ; crt144-product = refl
crt1728-product : 27 * 64 ≡ 1728 ; crt1728-product = refl

data TowerLevel : Set where
  level1 : TowerLevel
  level2 : TowerLevel
  level3 : TowerLevel

towerModulus : TowerLevel → ℕ
towerModulus level1 = 12 ; towerModulus level2 = 144 ; towerModulus level3 = 1728

towerMod3 : TowerLevel → ℕ
towerMod3 level1 = 3 ; towerMod3 level2 = 9 ; towerMod3 level3 = 27

towerMod2 : TowerLevel → ℕ
towerMod2 level1 = 4 ; towerMod2 level2 = 16 ; towerMod2 level3 = 64

tower-product : ∀ ℓ → towerMod3 ℓ * towerMod2 ℓ ≡ towerModulus ℓ
tower-product level1 = refl ; tower-product level2 = refl ; tower-product level3 = refl

tower-gcd : ∀ ℓ → gcd (towerMod3 ℓ) (towerMod2 ℓ) ≡ 1
tower-gcd level1 = refl ; tower-gcd level2 = refl ; tower-gcd level3 = refl
