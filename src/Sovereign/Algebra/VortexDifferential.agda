{-# OPTIONS --rewriting --guardedness #-}
module Sovereign.Algebra.VortexDifferential where

--------------------------------------------------------------------------------
-- Z/12Z 涡旋环上的差分算子与 Leibniz 规则
--
-- 代数链扩展 (Duodecimal L8-L10 之后):
--   L11: VortexFunc = Duodec → Trit — Z/12Z 上的 GF(3) 值函数空间
--   L12: Δ₁₂ 差分算子 — Δ₁₂f(x) = f(x+1) ⊕ negate(f(x))
--   L13: 卷积代数 — (f *₁₂ g)(x) = Σ_y f(y) ⊗ g(x ⊖ y)
--   L14: Leibniz 规则 — Δ₁₂(f *₁₂ g) = f *₁₂ (Δ₁₂ g)
--
-- 关键数学:
--   Z/12Z 上 Δ₁₂³ ≢ 0 (与 GF(3) 上的 Δ³ ≡ 0 不同!)
--   因为 (S-I)³ = S³-I (char 3), 而 S³ ≠ I on Z/12Z
--   正确性质: Δ₁₂³ f(x) = f(x+3) ⊕ negate(f(x)) (三步差分)
--
--   Leibniz 规则对任何循环群成立 (与特征无关):
--   Δ₁₂(f*g)(x) = Σ_y f(y)·(Δ₁₂g)(x-y) = (f * Δ₁₂g)(x)
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Function using (_|>_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (
  _≡_; refl; cong; cong₂; sym; trans; subst)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; negate²;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse;
  ⊗-comm; ⊗-assoc; ⊗-distribˡ-⊕; ⊗-distribʳ-⊕;
  ⊗-identityˡ; ⊗-identityʳ; ⊗-zeroˡ; ⊗-zeroʳ)

open import Sovereign.Algebra.Duodecimal using (
  Duodec; d0; d1; d2; d3; d4; d5; d6; d7; d8; d9; d10; d11;
  _+12_; +1; neg12; toℕ₁₂;
  +12-assoc; +12-comm; +12-identityˡ; +12-identityʳ;
  +12-inverse; +1-dist; shiftʳ)

--------------------------------------------------------------------------------
-- §1. 函数空间与基本算子
--------------------------------------------------------------------------------

VortexFunc : Set
VortexFunc = Duodec → Trit

_⊕f_ : VortexFunc → VortexFunc → VortexFunc
(f ⊕f g) x = f x ⊕ g x

negatef : VortexFunc → VortexFunc
negatef f x = negate (f x)

_·f_ : Trit → VortexFunc → VortexFunc
(s ·f f) x = s ⊗ f x

_≋_ : VortexFunc → VortexFunc → Set
f ≋ g = ∀ x → f x ≡ g x

shift₁₂ : VortexFunc → VortexFunc
shift₁₂ f x = f (+1 x)

Δ₁₂ : VortexFunc → VortexFunc
Δ₁₂ f x = f (+1 x) ⊕ negate (f x)

-- 12 点求和 (显式左结合)
sum12 : (Duodec → Trit) → Trit
sum12 h = (((((((((((h d0) ⊕ (h d1)) ⊕ (h d2)) ⊕ (h d3))
           ⊕ (h d4)) ⊕ (h d5)) ⊕ (h d6)) ⊕ (h d7))
           ⊕ (h d8)) ⊕ (h d9)) ⊕ (h d10)) ⊕ (h d11)

Σ₁₂ : VortexFunc → Trit
Σ₁₂ f = sum12 f

const₁₂ : Trit → VortexFunc
const₁₂ s _ = s

--------------------------------------------------------------------------------
-- §2. GF(3) 辅助引理
--------------------------------------------------------------------------------

negate-⊗ : ∀ x y → negate (x ⊗ y) ≡ negate x ⊗ y
negate-⊗ T₀ T₀ = refl; negate-⊗ T₀ T₁ = refl; negate-⊗ T₀ T₂ = refl
negate-⊗ T₁ T₀ = refl; negate-⊗ T₁ T₁ = refl; negate-⊗ T₁ T₂ = refl
negate-⊗ T₂ T₀ = refl; negate-⊗ T₂ T₁ = refl; negate-⊗ T₂ T₂ = refl

negate-⊗ʳ : ∀ x y → negate (x ⊗ y) ≡ x ⊗ negate y
negate-⊗ʳ T₀ T₀ = refl; negate-⊗ʳ T₀ T₁ = refl; negate-⊗ʳ T₀ T₂ = refl
negate-⊗ʳ T₁ T₀ = refl; negate-⊗ʳ T₁ T₁ = refl; negate-⊗ʳ T₁ T₂ = refl
negate-⊗ʳ T₂ T₀ = refl; negate-⊗ʳ T₂ T₁ = refl; negate-⊗ʳ T₂ T₂ = refl

negate-double : ∀ a → negate a ⊕ negate a ≡ a
negate-double T₀ = refl; negate-double T₁ = refl; negate-double T₂ = refl

-- negate 分配过 ⊕: negate(a ⊕ b) = negate a ⊕ negate b
negate-⊕ : ∀ a b → negate (a ⊕ b) ≡ negate a ⊕ negate b
negate-⊕ T₀ T₀ = refl; negate-⊕ T₀ T₁ = refl; negate-⊕ T₀ T₂ = refl
negate-⊕ T₁ T₀ = refl; negate-⊕ T₁ T₁ = refl; negate-⊕ T₁ T₂ = refl
negate-⊕ T₂ T₀ = refl; negate-⊕ T₂ T₁ = refl; negate-⊕ T₂ T₂ = refl

-- ⊕ 重排: (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
⊕-swap-mid : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
⊕-swap-mid a b c d =
  trans (⊕-assoc a b (c ⊕ d))
  (trans (cong (λ v → a ⊕ v) (⊕-comm b (c ⊕ d)))
  (trans (cong (λ v → a ⊕ v) (⊕-assoc c d b))
  (trans (cong (λ w → a ⊕ (c ⊕ w)) (⊕-comm d b))
         (sym (⊕-assoc a c (b ⊕ d))))))

--------------------------------------------------------------------------------
-- §3. 卷积定义 (通过 sum12)
--------------------------------------------------------------------------------

infixl 7 _*₁₂_
_*₁₂_ : VortexFunc → VortexFunc → VortexFunc
(f *₁₂ g) x = sum12 (λ y → f y ⊗ g (x +12 neg12 y))

--------------------------------------------------------------------------------
-- §4. Z/12Z 减法辅助引理
--------------------------------------------------------------------------------

+1-⊖-dist : ∀ x y → +1 (x +12 neg12 y) ≡ (+1 x) +12 neg12 y
+1-⊖-dist x y = +1-dist x (neg12 y)

--------------------------------------------------------------------------------
-- §5. 差分算子的基本性质
--------------------------------------------------------------------------------

-- 定理 1: Δ₁₂(f+g) = Δ₁₂f + Δ₁₂g
Δ₁₂-linear : ∀ f g → Δ₁₂ (f ⊕f g) ≋ (Δ₁₂ f ⊕f Δ₁₂ g)
Δ₁₂-linear f g x = lin-helper (f (+1 x)) (g (+1 x)) (f x) (g x)
  where
    lin-helper : ∀ a b c d → (a ⊕ b) ⊕ negate (c ⊕ d) ≡ (a ⊕ negate c) ⊕ (b ⊕ negate d)
    lin-helper T₀ T₀ T₀ T₀ = refl
    lin-helper T₀ T₀ T₀ T₁ = refl
    lin-helper T₀ T₀ T₀ T₂ = refl
    lin-helper T₀ T₀ T₁ T₀ = refl
    lin-helper T₀ T₀ T₁ T₁ = refl
    lin-helper T₀ T₀ T₁ T₂ = refl
    lin-helper T₀ T₀ T₂ T₀ = refl
    lin-helper T₀ T₀ T₂ T₁ = refl
    lin-helper T₀ T₀ T₂ T₂ = refl
    lin-helper T₀ T₁ T₀ T₀ = refl
    lin-helper T₀ T₁ T₀ T₁ = refl
    lin-helper T₀ T₁ T₀ T₂ = refl
    lin-helper T₀ T₁ T₁ T₀ = refl
    lin-helper T₀ T₁ T₁ T₁ = refl
    lin-helper T₀ T₁ T₁ T₂ = refl
    lin-helper T₀ T₁ T₂ T₀ = refl
    lin-helper T₀ T₁ T₂ T₁ = refl
    lin-helper T₀ T₁ T₂ T₂ = refl
    lin-helper T₀ T₂ T₀ T₀ = refl
    lin-helper T₀ T₂ T₀ T₁ = refl
    lin-helper T₀ T₂ T₀ T₂ = refl
    lin-helper T₀ T₂ T₁ T₀ = refl
    lin-helper T₀ T₂ T₁ T₁ = refl
    lin-helper T₀ T₂ T₁ T₂ = refl
    lin-helper T₀ T₂ T₂ T₀ = refl
    lin-helper T₀ T₂ T₂ T₁ = refl
    lin-helper T₀ T₂ T₂ T₂ = refl
    lin-helper T₁ T₀ T₀ T₀ = refl
    lin-helper T₁ T₀ T₀ T₁ = refl
    lin-helper T₁ T₀ T₀ T₂ = refl
    lin-helper T₁ T₀ T₁ T₀ = refl
    lin-helper T₁ T₀ T₁ T₁ = refl
    lin-helper T₁ T₀ T₁ T₂ = refl
    lin-helper T₁ T₀ T₂ T₀ = refl
    lin-helper T₁ T₀ T₂ T₁ = refl
    lin-helper T₁ T₀ T₂ T₂ = refl
    lin-helper T₁ T₁ T₀ T₀ = refl
    lin-helper T₁ T₁ T₀ T₁ = refl
    lin-helper T₁ T₁ T₀ T₂ = refl
    lin-helper T₁ T₁ T₁ T₀ = refl
    lin-helper T₁ T₁ T₁ T₁ = refl
    lin-helper T₁ T₁ T₁ T₂ = refl
    lin-helper T₁ T₁ T₂ T₀ = refl
    lin-helper T₁ T₁ T₂ T₁ = refl
    lin-helper T₁ T₁ T₂ T₂ = refl
    lin-helper T₁ T₂ T₀ T₀ = refl
    lin-helper T₁ T₂ T₀ T₁ = refl
    lin-helper T₁ T₂ T₀ T₂ = refl
    lin-helper T₁ T₂ T₁ T₀ = refl
    lin-helper T₁ T₂ T₁ T₁ = refl
    lin-helper T₁ T₂ T₁ T₂ = refl
    lin-helper T₁ T₂ T₂ T₀ = refl
    lin-helper T₁ T₂ T₂ T₁ = refl
    lin-helper T₁ T₂ T₂ T₂ = refl
    lin-helper T₂ T₀ T₀ T₀ = refl
    lin-helper T₂ T₀ T₀ T₁ = refl
    lin-helper T₂ T₀ T₀ T₂ = refl
    lin-helper T₂ T₀ T₁ T₀ = refl
    lin-helper T₂ T₀ T₁ T₁ = refl
    lin-helper T₂ T₀ T₁ T₂ = refl
    lin-helper T₂ T₀ T₂ T₀ = refl
    lin-helper T₂ T₀ T₂ T₁ = refl
    lin-helper T₂ T₀ T₂ T₂ = refl
    lin-helper T₂ T₁ T₀ T₀ = refl
    lin-helper T₂ T₁ T₀ T₁ = refl
    lin-helper T₂ T₁ T₀ T₂ = refl
    lin-helper T₂ T₁ T₁ T₀ = refl
    lin-helper T₂ T₁ T₁ T₁ = refl
    lin-helper T₂ T₁ T₁ T₂ = refl
    lin-helper T₂ T₁ T₂ T₀ = refl
    lin-helper T₂ T₁ T₂ T₁ = refl
    lin-helper T₂ T₁ T₂ T₂ = refl
    lin-helper T₂ T₂ T₀ T₀ = refl
    lin-helper T₂ T₂ T₀ T₁ = refl
    lin-helper T₂ T₂ T₀ T₂ = refl
    lin-helper T₂ T₂ T₁ T₀ = refl
    lin-helper T₂ T₂ T₁ T₁ = refl
    lin-helper T₂ T₂ T₁ T₂ = refl
    lin-helper T₂ T₂ T₂ T₀ = refl
    lin-helper T₂ T₂ T₂ T₁ = refl
    lin-helper T₂ T₂ T₂ T₂ = refl

-- 定理 2: Δ₁₂(s·f) = s·Δ₁₂f
Δ₁₂-scalar : ∀ s f → Δ₁₂ (s ·f f) ≋ (s ·f Δ₁₂ f)
Δ₁₂-scalar s f x =
  trans (cong (λ v → (s ⊗ f (+1 x)) ⊕ v) (negate-⊗ʳ s (f x)))
        (sym (⊗-distribˡ-⊕ s (f (+1 x)) (negate (f x))))

-- 定理 3: Δ₁₂(shift₁₂ f) = shift₁₂(Δ₁₂ f) [refl]
shift₁₂-comm : ∀ f → Δ₁₂ (shift₁₂ f) ≋ shift₁₂ (Δ₁₂ f)
shift₁₂-comm f x = refl

-- 定理 5: Δ₁₂(const₁₂ s) = const₁₂ T₀
Δ₁₂-const-zero : ∀ s → Δ₁₂ (const₁₂ s) ≋ const₁₂ T₀
Δ₁₂-const-zero s x = ⊕-inverse s

sum₁₂-annihilation : ∀ s → Δ₁₂ (const₁₂ s) ≋ const₁₂ T₀
sum₁₂-annihilation = Δ₁₂-const-zero

--------------------------------------------------------------------------------
-- §6. 三步差分 — Δ₁₂³ f(x) = f(x+3) ⊕ negate(f(x))
--------------------------------------------------------------------------------

+1³ : Duodec → Duodec
+1³ x = +1 (+1 (+1 x))

-- 辅助引理: GF(3) 中 negate a ⊕ negate a ≡ a (因为 -2 ≡ 1 mod 3)

-- 辅助引理: Δ₁₂²f(x) = f(x+2) ⊕ (f(x+1) ⊕ f(x))
-- 证明: 代数链 (negate-⊕ → negate² → assoc → negate-double)
Δ₁₂²-expand : ∀ f x →
  Δ₁₂ (Δ₁₂ f) x ≡ (f (+1 (+1 x)) ⊕ (f (+1 x) ⊕ f x))
Δ₁₂²-expand f x =
  trans (cong (λ v → (f (+1 (+1 x)) ⊕ negate (f (+1 x))) ⊕ v)
              (trans (negate-⊕ (f (+1 x)) (negate (f x)))
                     (cong (negate (f (+1 x)) ⊕_) (negate² (f x)))))
  (trans (⊕-assoc (f (+1 (+1 x))) (negate (f (+1 x))) (negate (f (+1 x)) ⊕ f x))
  (trans (cong (λ v → f (+1 (+1 x)) ⊕ v)
              (sym (⊕-assoc (negate (f (+1 x))) (negate (f (+1 x))) (f x))))
  (cong (λ w → f (+1 (+1 x)) ⊕ (w ⊕ f x))
        (negate-double (f (+1 x))))))

-- 核心消去引理: (a ⊕ negate b) ⊕ (b ⊕ c) ≡ a ⊕ c
-- 证明: assoc → sym assoc → comm+inverse → identity (4 步代数链)
cancel-pair : ∀ a b c → (a ⊕ negate b) ⊕ (b ⊕ c) ≡ a ⊕ c
cancel-pair a b c =
  trans (⊕-assoc a (negate b) (b ⊕ c))
  (trans (cong (a ⊕_) (sym (⊕-assoc (negate b) b c)))
  (trans (cong (λ v → a ⊕ (v ⊕ c)) (trans (⊕-comm (negate b) b) (⊕-inverse b)))
         (cong (a ⊕_) (⊕-identityˡ c))))

-- 内层望远镜: negate c ⊕ (c ⊕ negate d) ≡ negate d
-- 证明: sym assoc → comm+inverse → identity (3 步代数链)
inner-telescope : ∀ c d → negate c ⊕ (c ⊕ negate d) ≡ negate d
inner-telescope c d =
  trans (sym (⊕-assoc (negate c) c (negate d)))
  (trans (cong (_⊕ negate d) (trans (⊕-comm (negate c) c) (⊕-inverse c)))
         (⊕-identityˡ (negate d)))

-- 完全展开: (a⊕negate b)⊕((b⊕negate c)⊕(c⊕negate d)) ≡ a⊕negate d
-- 证明: assoc → cancel-pair → inner-telescope (3 步)
telescope-4 : ∀ a b c d → (a ⊕ negate b) ⊕ ((b ⊕ negate c) ⊕ (c ⊕ negate d)) ≡ a ⊕ negate d
telescope-4 a b c d =
  trans (cong ((a ⊕ negate b) ⊕_) (⊕-assoc b (negate c) (c ⊕ negate d)))
  (trans (cancel-pair a b (negate c ⊕ (c ⊕ negate d)))
         (cong (a ⊕_) (inner-telescope c d)))

-- 定理 4: Δ₁₂³ f(x) = f(x+3) ⊕ negate(f(x))
-- 证明: Δ₁₂²-expand → telescope-4 (2 步)
Δ₁₂³-is-3step : ∀ f x →
  Δ₁₂ (Δ₁₂ (Δ₁₂ f)) x ≡ (f (+1 (+1 (+1 x))) ⊕ negate (f x))
Δ₁₂³-is-3step f x =
  trans (Δ₁₂²-expand (Δ₁₂ f) x)
        (telescope-4 (f (+1 (+1 (+1 x)))) (f (+1 (+1 x))) (f (+1 x)) (f x))

--------------------------------------------------------------------------------
-- §7. 卷积的移位交换性
--------------------------------------------------------------------------------

shift-conv : ∀ f g → shift₁₂ (f *₁₂ g) ≋ (f *₁₂ shift₁₂ g)
shift-conv f g x =
  cong₂ _⊕_
    (cong₂ _⊕_
      (cong₂ _⊕_
        (cong₂ _⊕_
          (cong₂ _⊕_
            (cong₂ _⊕_
              (cong₂ _⊕_
                (cong₂ _⊕_
                  (cong₂ _⊕_
                    (cong₂ _⊕_
                      (cong₂ _⊕_
                        (cong (f d0 ⊗_) (cong g (sym (+1-⊖-dist x d0))))
                        (cong (f d1 ⊗_) (cong g (sym (+1-⊖-dist x d1)))))
                      (cong (f d2 ⊗_) (cong g (sym (+1-⊖-dist x d2)))))
                    (cong (f d3 ⊗_) (cong g (sym (+1-⊖-dist x d3)))))
                  (cong (f d4 ⊗_) (cong g (sym (+1-⊖-dist x d4)))))
                (cong (f d5 ⊗_) (cong g (sym (+1-⊖-dist x d5)))))
              (cong (f d6 ⊗_) (cong g (sym (+1-⊖-dist x d6)))))
            (cong (f d7 ⊗_) (cong g (sym (+1-⊖-dist x d7)))))
          (cong (f d8 ⊗_) (cong g (sym (+1-⊖-dist x d8)))))
        (cong (f d9 ⊗_) (cong g (sym (+1-⊖-dist x d9)))))
      (cong (f d10 ⊗_) (cong g (sym (+1-⊖-dist x d10)))))
    (cong (f d11 ⊗_) (cong g (sym (+1-⊖-dist x d11))))


--------------------------------------------------------------------------------
-- §8-§10 (sum12-distrib, 卷积线性性, Leibniz 规则) 待后续用代数链风格重写
-- 核心定理 §1-§7 已正确: Δ₁₂-linear, cancel-pair, Δ₁₂³-is-3step, Δ₁₂-const-zero
--------------------------------------------------------------------------------
