------------------------------------------------------------------------
-- | Sovereign.Problem.Sqrt2.Sqrt2Irrational
-- √2 是无理数 — 完整形式化证明
--
-- 数学背景:
--   √2 ∉ ℚ。表述为自然数对: 不存在 a b : ℕ, b ≢ 0 且 a² = 2·b²
--   （若有既约分数 p/q 满足 (p/q)² = 2，即得这样的 (p, q)，矛盾）。
--
-- 证法（Euler 无穷递降，良基化）:
--   · ℕ 上完全奇偶性：奇数平方是奇数而 2·b² 是偶数，
--     故 a² = 2·b² 蕴含 a = 2·a₁（square-dub→even）。
--   · 回代得 b² = 2·a₁²，同理 b = 2·b₁ 且 a₁² = 2·b₁²（递降步）。
--   · a₁ ≤ a-1；把命题强化为 Strong n =「≤ n 的一切 m 都无解」，
--     随 n 结构递归即闭合无穷递降（无需 Acc/良基机器）。
--
-- 自包含：仅依赖 Agda 内建（Nat、_≡_），不依赖 standard library。
-- 零 postulate、零 hole。
------------------------------------------------------------------------

module Sovereign.Problem.Sqrt2.Sqrt2Irrational where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- 逻辑工具

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

¬ : Set → Set
¬ A = A → ⊥

_≢_ : Nat → Nat → Set
a ≢ b = a ≡ b → ⊥

infix 4 _≢_

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

infixr 4 _,_

open Σ public

------------------------------------------------------------------------
-- 加法引理

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-zeroʳ : ∀ n → n + zero ≡ n
+-zeroʳ zero    = refl
+-zeroʳ (suc n) = cong suc (+-zeroʳ n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-zeroʳ n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-swap : ∀ a b c → a + (b + c) ≡ b + (a + c)
+-swap a b c =
  trans (sym (+-assoc a b c))
    (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

------------------------------------------------------------------------
-- 乘法引理

*-zeroʳ : ∀ n → n * zero ≡ zero
*-zeroʳ zero    = refl
*-zeroʳ (suc n) = *-zeroʳ n

*-suc : ∀ m n → m * suc n ≡ m + m * n
*-suc zero    n = refl
*-suc (suc m) n =
  cong suc (trans (cong (n +_) (*-suc m n)) (+-swap n m (m * n)))

*-comm : ∀ m n → m * n ≡ n * m
*-comm zero    n = sym (*-zeroʳ n)
*-comm (suc m) n = trans (cong (n +_) (*-comm m n)) (sym (*-suc n m))

*-distribˡ : ∀ a b c → (a + b) * c ≡ a * c + b * c
*-distribˡ zero    b c = refl
*-distribˡ (suc a) b c =
  trans (cong (c +_) (*-distribˡ a b c)) (sym (+-assoc c (a * c) (b * c)))

------------------------------------------------------------------------
-- 翻倍 dub n = 2·n

dub : Nat → Nat
dub n = n + n

*-dubˡ : ∀ a b → dub a * b ≡ dub (a * b)
*-dubˡ a b = *-distribˡ a a b

*-dubʳ : ∀ a b → a * dub b ≡ dub (a * b)
*-dubʳ a b =
  trans (*-comm a (dub b)) (trans (*-dubˡ b a) (cong dub (*-comm b a)))

*-dub² : ∀ k → dub k * dub k ≡ dub (dub (k * k))
*-dub² k = trans (*-dubˡ k (dub k)) (cong dub (*-dubʳ k k))

dub-+ : ∀ p q → dub p + dub q ≡ dub (p + q)
dub-+ p q =
  trans (+-assoc p p (q + q))
    (trans (cong (p +_) (trans (sym (+-assoc p q q)) (+-comm (p + q) q)))
           (sym (+-assoc p q (p + q))))

------------------------------------------------------------------------
-- 完全奇偶性

data Even (n : Nat) : Set where
  even : (k : Nat) → n ≡ dub k → Even n

data Odd (n : Nat) : Set where
  odd : (k : Nat) → n ≡ suc (dub k) → Odd n

suc-dub : ∀ n k → n ≡ suc (dub k) → suc n ≡ dub (suc k)
suc-dub n k ek =
  trans (cong suc ek) (sym (cong suc (+-suc k k)))

parity : ∀ n → Even n ⊎ Odd n
parity zero    = inj₁ (even zero refl)
parity (suc n) with parity n
... | inj₁ (even k ek) = inj₂ (odd k (cong suc ek))
... | inj₂ (odd k ek)  = inj₁ (even (suc k) (suc-dub n k ek))

------------------------------------------------------------------------
-- 奇偶不相容与单射性

suc-inj : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

zero≠suc : ∀ {n : Nat} → zero ≡ suc n → ⊥
zero≠suc ()

-- 偶 ≠ 奇（对 x 归纳，y 概括）
¬dub-sucdub : ∀ x y → dub x ≢ suc (dub y)
¬dub-sucdub zero    y          ()
¬dub-sucdub (suc x') zero     eq =
  zero≠suc (trans (sym (suc-inj eq)) (+-suc x' x'))
¬dub-sucdub (suc x') (suc y') eq =
  ¬dub-sucdub x' y'
    (trans (suc-inj (trans (sym (+-suc x' x')) (suc-inj eq)))
           (+-suc y' y'))

dub-inj : ∀ x y → dub x ≡ dub y → x ≡ y
dub-inj zero    zero     _  = refl
dub-inj zero    (suc y') ()
dub-inj (suc x') zero    ()
dub-inj (suc x') (suc y') eq =
  cong suc (dub-inj x' y'
    (suc-inj (trans (sym (+-comm x' (suc x')))
                    (trans (suc-inj eq) (+-comm y' (suc y'))))))

dub-zero : ∀ x → dub x ≡ zero → x ≡ zero
dub-zero zero     _  = refl
dub-zero (suc x') ()

sq-zero : ∀ b → b * b ≡ zero → b ≡ zero
sq-zero zero     _  = refl
sq-zero (suc b') ()

------------------------------------------------------------------------
-- 奇数的平方是奇数：(2k+1)² = 2·(2k + k²) + 1

odd-square : ∀ k → Σ Nat (λ t → suc (dub k) * suc (dub k) ≡ suc (dub t))
odd-square k = dub k + dub (k * k) ,
  trans (cong (λ w → suc (dub k + w)) (*-suc (dub k) (dub k)))
  (trans (cong (λ w → suc (dub k + (dub k + w))) (*-dub² k))
  (trans (cong suc (sym (+-assoc (dub k) (dub k) (dub (dub (k * k))))))
         (cong suc (dub-+ (dub k) (dub (k * k))))))

------------------------------------------------------------------------
-- 平方等于二倍平方者必为偶

square-dub→even : ∀ a b → a * a ≡ dub (b * b) → Σ Nat (λ k → a ≡ dub k)
square-dub→even a b eq with parity a
... | inj₁ (even k ek) = k , ek
... | inj₂ (odd k ok) with odd-square k
...   | (t , sq) =
        ⊥-elim (¬dub-sucdub (b * b) t
          (sym (trans (sym (trans (cong (λ z → z * z) ok) sq)) eq)))

square-dub→even⁺ :
  ∀ a b → a * a ≡ dub (b * b) → b ≢ zero → Σ Nat (λ k → a ≡ dub (suc k))
square-dub→even⁺ a b eq b≠0 with square-dub→even a b eq
... | (zero , ea) =
      ⊥-elim (b≠0 (sq-zero b (dub-zero (b * b)
        (trans (sym eq) (cong (λ z → z * z) ea)))))
... | (suc k , ek) = k , ek

------------------------------------------------------------------------
-- 序与替换工具（自包含，不依赖 stdlib）

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

≤-substʳ : ∀ {k x y : Nat} → x ≡ y → k ≤ x → k ≤ y
≤-substʳ refl p = p

≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-zero : ∀ m → m ≤ zero → m ≡ zero
≤-zero zero    z≤n = refl
≤-zero (suc m) ()

≤-inv : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-inv (s≤s p) = p

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n     _      = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

m≤+ : ∀ k x → k ≤ k + x
m≤+ zero    x = z≤n
m≤+ (suc k) x = s≤s (m≤+ k x)

subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

------------------------------------------------------------------------
-- 主定理

NoPair : Nat → Set
NoPair a = ∀ (b : Nat) → b ≢ zero → a * a ≢ dub (b * b)

noPair-zero : NoPair zero
noPair-zero b b≠0 eq = b≠0 (sq-zero b (dub-zero (b * b) (sym eq)))

-- 递降步：解 (suc a', b) 的两半 (suc k₀, suc k₁) 仍是解，且 suc k₀ ≤ a'
descent-suc :
  ∀ (a' : Nat) → (∀ (m : Nat) → m ≤ a' → NoPair m)
  → ∀ (b : Nat) → b ≢ zero → suc a' * suc a' ≡ dub (b * b) → ⊥
descent-suc a' IH b b≠0 eq =
  ⊥-elim (IH (suc k₀) lt (suc k₁) (λ ()) eq')
  where
  k₀  = proj₁ (square-dub→even⁺ (suc a') b eq b≠0)
  ek₀ = proj₂ (square-dub→even⁺ (suc a') b eq b≠0)
  e2 : a' ≡ suc (k₀ + k₀)
  e2 = trans (suc-inj ek₀) (+-suc k₀ k₀)
  lt : suc k₀ ≤ a'
  lt = ≤-substʳ (sym e2) (s≤s (m≤+ k₀ k₀))
  sq₁ : suc a' * suc a' ≡ dub (dub (suc k₀ * suc k₀))
  sq₁ = trans (cong (λ z → z * z) ek₀) (*-dub² (suc k₀))
  eqR : dub (dub (suc k₀ * suc k₀)) ≡ dub (b * b)
  eqR = trans (sym sq₁) eq
  eqb0 : b * b ≡ dub (suc k₀ * suc k₀)
  eqb0 = dub-inj (b * b) (dub (suc k₀ * suc k₀)) (sym eqR)
  k₁  = proj₁ (square-dub→even⁺ b (suc k₀) eqb0 (λ ()))
  ek₁ = proj₂ (square-dub→even⁺ b (suc k₀) eqb0 (λ ()))
  bb₂ : b * b ≡ dub (dub (suc k₁ * suc k₁))
  bb₂ = trans (cong (λ z → z * z) ek₁) (*-dub² (suc k₁))
  sub : dub (dub (suc k₀ * suc k₀)) ≡ dub (dub (dub (suc k₁ * suc k₁)))
  sub = trans eqR (cong dub bb₂)
  eq' : suc k₀ * suc k₀ ≡ dub (suc k₁ * suc k₁)
  eq' = dub-inj (suc k₀ * suc k₀) (dub (suc k₁ * suc k₁))
          (dub-inj (dub (suc k₀ * suc k₀)) (dub (dub (suc k₁ * suc k₁))) sub)

-- 强化归纳命题：Strong n =「≤ n 的一切 m 都无解」，随 n 结构递归闭合递降
Strong : Nat → Set
Strong n = ∀ (m : Nat) → m ≤ n → NoPair m

strong-suc : ∀ n → Strong n → Strong (suc n)
strong-suc n IH m m≤sucn with m
... | zero    = noPair-zero
... | suc m'  =
        descent-suc m' (λ x x≤m' → IH x (≤-trans x≤m' (≤-inv m≤sucn)))

strong : ∀ n → Strong n
strong zero    = λ m m≤0 → subst NoPair (sym (≤-zero m m≤0)) noPair-zero
strong (suc n) = strong-suc n (strong n)

sqrt2-pair-absurd : ∀ (a b : Nat) → b ≢ zero → a * a ≢ dub (b * b)
sqrt2-pair-absurd a b b≠0 eq = strong a a (≤-refl a) b b≠0 eq

------------------------------------------------------------------------
-- 定理：√2 是无理数
-- 不存在自然数对 (a, b)：b ≢ 0 且 a² = 2·b²。
-- （既约分数 p/q 满足 (p/q)² = 2 将给出这样的对，矛盾。）

sqrt2-irrational :
  ¬ (Σ Nat (λ a → Σ Nat (λ b → Σ (b ≢ zero) (λ _ → a * a ≡ dub (b * b)))))
sqrt2-irrational (a , b , b≠0 , eq) = sqrt2-pair-absurd a b b≠0 eq
