{-# OPTIONS --rewriting #-}

-- | Sovereign.Application.ProjectiveCore
-- 4320D 射影几何核心：规范群 G = (C₃)³ ⋊ C₂ + 射影点 = G-不可约轨道
--
-- G = (C₃ × C₃ × C₃) ⋊ C₂, |G| = 54
-- 信息 = 群轨道, 非 βη 语法等价

module Sovereign.Application.ProjectiveCore where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Synthesis.T6 using (T6Lattice)

--------------------------------------------------------------------------------
-- 1. Fin 3 上的 C₃ 与 C₂ 作用
--------------------------------------------------------------------------------

tritOf : Fin 3 → Trit
tritOf zero = T₀
tritOf (suc zero) = T₁
tritOf (suc (suc zero)) = T₂

-- C₃: x → x+1 mod 3
c3 : Fin 3 → Fin 3
c3 x = tritToFin (tritOf x ⊕ T₁)
  where
    tritToFin : Trit → Fin 3
    tritToFin T₀ = zero
    tritToFin T₁ = suc zero
    tritToFin T₂ = suc (suc zero)

-- C₂: 手征反转 T₁↔T₂ (Frobenius)
c2 : Fin 3 → Fin 3
c2 x = tritToFin (swp (tritOf x))
  where
    tritToFin : Trit → Fin 3
    tritToFin T₀ = zero
    tritToFin T₁ = suc zero
    tritToFin T₂ = suc (suc zero)
    swp : Trit → Trit
    swp T₀ = T₀
    swp T₁ = T₂
    swp T₂ = T₁

--------------------------------------------------------------------------------
-- 2. G = (C₃)³ ⋊ C₂
--------------------------------------------------------------------------------

-- 使用 record 避免元组解析问题
record C3Triple : Set where
  constructor c3₃
  field a b c : Fin 3

record GElement : Set where
  constructor ⟨_,_⟩
  field rot : C3Triple
        chi : Fin 2

g-id : GElement
g-id = ⟨ c3₃ zero zero zero , zero ⟩

_+₃_ : Fin 3 → Fin 3 → Fin 3
x +₃ y = tritToFin (tritOf x ⊕ tritOf y)
  where
    tritToFin : Trit → Fin 3
    tritToFin T₀ = zero
    tritToFin T₁ = suc zero
    tritToFin T₂ = suc (suc zero)

_+₂_ : Fin 2 → Fin 2 → Fin 2
zero +₂ y = y
suc x +₂ zero = suc x
suc x +₂ suc y = zero  -- 1+1 ≡ 0 mod 2

g-mul : GElement → GElement → GElement
g-mul ⟨ c3₃ a₁ b₁ c₁ , h₁ ⟩ ⟨ c3₃ a₂ b₂ c₂ , h₂ ⟩ =
  ⟨ c3₃ (a₁ +₃ a₂) (b₁ +₃ b₂) (c₁ +₃ c₂) , h₁ +₂ h₂ ⟩

neg3 : Fin 3 → Fin 3
neg3 zero = zero
neg3 (suc zero) = suc (suc zero)
neg3 (suc (suc zero)) = suc zero

neg3-invol : ∀ x → neg3 (neg3 x) ≡ x
neg3-invol zero = refl
neg3-invol (suc zero) = refl
neg3-invol (suc (suc zero)) = refl

g-inv : GElement → GElement
g-inv ⟨ c3₃ a b c , h ⟩ = ⟨ c3₃ (neg3 a) (neg3 b) (neg3 c) , h ⟩

--------------------------------------------------------------------------------
-- 3. G 在 T⁶ 上的作用
--------------------------------------------------------------------------------

c3ⁿ : Fin 3 → Fin 3 → Fin 3  -- 幂次 × 坐标
c3ⁿ zero    x = x
c3ⁿ (suc zero)    x = c3 x
c3ⁿ (suc (suc zero)) x = c3 (c3 x)

g-action : GElement → T6Lattice → T6Lattice
g-action ⟨ c3₃ a b c , h ⟩ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  c3ⁿ a x₀ ∷ c3ⁿ b x₁ ∷ c3ⁿ c x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []

g-action-full : GElement → T6Lattice → T6Lattice
g-action-full g@(⟨ _ , zero ⟩) v = g-action g v
g-action-full g@(⟨ c3₃ a b c , suc _ ⟩) (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  c2 (c3ⁿ a x₀) ∷ c2 (c3ⁿ b x₁) ∷ c2 (c3ⁿ c x₂) ∷
  c2 x₃ ∷ c2 x₄ ∷ c2 x₅ ∷ []

--------------------------------------------------------------------------------
-- 4. G-轨道 = 射影点
--------------------------------------------------------------------------------

record GOrbitRel (x y : T6Lattice) : Set where
  constructor g-orbit-path
  field g   : GElement
        eq  : g-action-full g x ≡ y

GOrbit : T6Lattice → Set
GOrbit x = Σ T6Lattice (λ y → GOrbitRel x y)

record ProjectivePointRec : Set where
  constructor mk-point
  field rep   : T6Lattice
        orbit : GOrbit rep

-- §5 群公理与轨道等价律（构造性——原 postulate 全消）
-- 策略：Fin 闭计算（27/9-case 归约）+ 轨道见证构造（仿射族 c2^h∘c3^t 对复合封闭）
-- 口径：豁免精化判据正解——群公理=结构公理、等价律=可导出件，零豁免零 postulate

c3₃-ext : ∀ {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → c3₃ a b c ≡ c3₃ a′ b′ c′
c3₃-ext refl refl refl = refl

v6 : ∀ {x₀ x₀′ x₁ x₁′ x₂ x₂′ x₃ x₃′ x₄ x₄′ x₅ x₅′ : Fin 3}
   → x₀ ≡ x₀′ → x₁ ≡ x₁′ → x₂ ≡ x₂′ → x₃ ≡ x₃′ → x₄ ≡ x₄′ → x₅ ≡ x₅′
   → (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) ≡ (x₀′ ∷ x₁′ ∷ x₂′ ∷ x₃′ ∷ x₄′ ∷ x₅′ ∷ [])
v6 refl refl refl refl refl refl = refl

+₃-zeroˡ : ∀ x → zero +₃ x ≡ x
+₃-zeroˡ zero = refl
+₃-zeroˡ (suc zero) = refl
+₃-zeroˡ (suc (suc zero)) = refl

+₃-zeroʳ : ∀ x → x +₃ zero ≡ x
+₃-zeroʳ zero = refl
+₃-zeroʳ (suc zero) = refl
+₃-zeroʳ (suc (suc zero)) = refl

+₃-assoc : ∀ x y z → (x +₃ y) +₃ z ≡ x +₃ (y +₃ z)
+₃-assoc zero zero zero = refl
+₃-assoc zero zero (suc zero) = refl
+₃-assoc zero zero (suc (suc zero)) = refl
+₃-assoc zero (suc zero) zero = refl
+₃-assoc zero (suc zero) (suc zero) = refl
+₃-assoc zero (suc zero) (suc (suc zero)) = refl
+₃-assoc zero (suc (suc zero)) zero = refl
+₃-assoc zero (suc (suc zero)) (suc zero) = refl
+₃-assoc zero (suc (suc zero)) (suc (suc zero)) = refl
+₃-assoc (suc zero) zero zero = refl
+₃-assoc (suc zero) zero (suc zero) = refl
+₃-assoc (suc zero) zero (suc (suc zero)) = refl
+₃-assoc (suc zero) (suc zero) zero = refl
+₃-assoc (suc zero) (suc zero) (suc zero) = refl
+₃-assoc (suc zero) (suc zero) (suc (suc zero)) = refl
+₃-assoc (suc zero) (suc (suc zero)) zero = refl
+₃-assoc (suc zero) (suc (suc zero)) (suc zero) = refl
+₃-assoc (suc zero) (suc (suc zero)) (suc (suc zero)) = refl
+₃-assoc (suc (suc zero)) zero zero = refl
+₃-assoc (suc (suc zero)) zero (suc zero) = refl
+₃-assoc (suc (suc zero)) zero (suc (suc zero)) = refl
+₃-assoc (suc (suc zero)) (suc zero) zero = refl
+₃-assoc (suc (suc zero)) (suc zero) (suc zero) = refl
+₃-assoc (suc (suc zero)) (suc zero) (suc (suc zero)) = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) zero = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) (suc zero) = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) (suc (suc zero)) = refl

+₃-negˡ : ∀ x → neg3 x +₃ x ≡ zero
+₃-negˡ zero = refl
+₃-negˡ (suc zero) = refl
+₃-negˡ (suc (suc zero)) = refl

+₃-negʳ : ∀ x → x +₃ neg3 x ≡ zero
+₃-negʳ zero = refl
+₃-negʳ (suc zero) = refl
+₃-negʳ (suc (suc zero)) = refl

+₂-self : ∀ h → h +₂ h ≡ zero
+₂-self zero = refl
+₂-self (suc zero) = refl

+₂-zeroʳ : ∀ h → h +₂ zero ≡ h
+₂-zeroʳ zero = refl
+₂-zeroʳ (suc zero) = refl

+₂-assoc : ∀ x y z → (x +₂ y) +₂ z ≡ x +₂ (y +₂ z)
+₂-assoc zero zero zero = refl
+₂-assoc zero zero (suc zero) = refl
+₂-assoc zero (suc zero) zero = refl
+₂-assoc zero (suc zero) (suc zero) = refl
+₂-assoc (suc zero) zero zero = refl
+₂-assoc (suc zero) zero (suc zero) = refl
+₂-assoc (suc zero) (suc zero) zero = refl
+₂-assoc (suc zero) (suc zero) (suc zero) = refl

g-id-chi : GElement.chi g-id ≡ zero
g-id-chi = refl

c3ⁿ-add : ∀ a b x → c3ⁿ (a +₃ b) x ≡ c3ⁿ a (c3ⁿ b x)
c3ⁿ-add zero zero zero = refl
c3ⁿ-add zero zero (suc zero) = refl
c3ⁿ-add zero zero (suc (suc zero)) = refl
c3ⁿ-add zero (suc zero) zero = refl
c3ⁿ-add zero (suc zero) (suc zero) = refl
c3ⁿ-add zero (suc zero) (suc (suc zero)) = refl
c3ⁿ-add zero (suc (suc zero)) zero = refl
c3ⁿ-add zero (suc (suc zero)) (suc zero) = refl
c3ⁿ-add zero (suc (suc zero)) (suc (suc zero)) = refl
c3ⁿ-add (suc zero) zero zero = refl
c3ⁿ-add (suc zero) zero (suc zero) = refl
c3ⁿ-add (suc zero) zero (suc (suc zero)) = refl
c3ⁿ-add (suc zero) (suc zero) zero = refl
c3ⁿ-add (suc zero) (suc zero) (suc zero) = refl
c3ⁿ-add (suc zero) (suc zero) (suc (suc zero)) = refl
c3ⁿ-add (suc zero) (suc (suc zero)) zero = refl
c3ⁿ-add (suc zero) (suc (suc zero)) (suc zero) = refl
c3ⁿ-add (suc zero) (suc (suc zero)) (suc (suc zero)) = refl
c3ⁿ-add (suc (suc zero)) zero zero = refl
c3ⁿ-add (suc (suc zero)) zero (suc zero) = refl
c3ⁿ-add (suc (suc zero)) zero (suc (suc zero)) = refl
c3ⁿ-add (suc (suc zero)) (suc zero) zero = refl
c3ⁿ-add (suc (suc zero)) (suc zero) (suc zero) = refl
c3ⁿ-add (suc (suc zero)) (suc zero) (suc (suc zero)) = refl
c3ⁿ-add (suc (suc zero)) (suc (suc zero)) zero = refl
c3ⁿ-add (suc (suc zero)) (suc (suc zero)) (suc zero) = refl
c3ⁿ-add (suc (suc zero)) (suc (suc zero)) (suc (suc zero)) = refl

c3ⁿ-inv : ∀ a x → c3ⁿ (neg3 a) (c3ⁿ a x) ≡ x
c3ⁿ-inv zero zero = refl
c3ⁿ-inv zero (suc zero) = refl
c3ⁿ-inv zero (suc (suc zero)) = refl
c3ⁿ-inv (suc zero) zero = refl
c3ⁿ-inv (suc zero) (suc zero) = refl
c3ⁿ-inv (suc zero) (suc (suc zero)) = refl
c3ⁿ-inv (suc (suc zero)) zero = refl
c3ⁿ-inv (suc (suc zero)) (suc zero) = refl
c3ⁿ-inv (suc (suc zero)) (suc (suc zero)) = refl

c2-invol : ∀ x → c2 (c2 x) ≡ x
c2-invol zero = refl
c2-invol (suc zero) = refl
c2-invol (suc (suc zero)) = refl

c2-c3ⁿ : ∀ a x → c2 (c3ⁿ a x) ≡ c3ⁿ (neg3 a) (c2 x)
c2-c3ⁿ zero zero = refl
c2-c3ⁿ zero (suc zero) = refl
c2-c3ⁿ zero (suc (suc zero)) = refl
c2-c3ⁿ (suc zero) zero = refl
c2-c3ⁿ (suc zero) (suc zero) = refl
c2-c3ⁿ (suc zero) (suc (suc zero)) = refl
c2-c3ⁿ (suc (suc zero)) zero = refl
c2-c3ⁿ (suc (suc zero)) (suc zero) = refl
c2-c3ⁿ (suc (suc zero)) (suc (suc zero)) = refl

-- 群公理（g-mul = 直积形——分量闭计算）
g-id-left : ∀ g → g-mul g-id g ≡ g
g-id-left ⟨ c3₃ a b c , h ⟩ =
  cong₂ ⟨_,_⟩ (c3₃-ext (+₃-zeroˡ a) (+₃-zeroˡ b) (+₃-zeroˡ c)) refl

g-id-right : ∀ g → g-mul g g-id ≡ g
g-id-right ⟨ c3₃ a b c , h ⟩ =
  cong₂ ⟨_,_⟩ (c3₃-ext (+₃-zeroʳ a) (+₃-zeroʳ b) (+₃-zeroʳ c))
    (trans (cong (h +₂_) g-id-chi) (+₂-zeroʳ h))

g-inv-left : ∀ g → g-mul (g-inv g) g ≡ g-id
g-inv-left ⟨ c3₃ a b c , h ⟩ =
  cong₂ ⟨_,_⟩ (c3₃-ext (+₃-negˡ a) (+₃-negˡ b) (+₃-negˡ c)) (+₂-self h)

g-assoc : ∀ g h k → g-mul (g-mul g h) k ≡ g-mul g (g-mul h k)
g-assoc ⟨ c3₃ a₁ b₁ c₁ , h₁ ⟩ ⟨ c3₃ a₂ b₂ c₂′ , h₂ ⟩ ⟨ c3₃ a₃ b₃ c₃′ , h₃ ⟩ =
  cong₂ ⟨_,_⟩ (c3₃-ext (+₃-assoc a₁ a₂ a₃) (+₃-assoc b₁ b₂ b₃) (+₃-assoc c₁ c₂′ c₃′))
    (+₂-assoc h₁ h₂ h₃)

-- 轨道等价律（见证构造：仿射族闭包——注意 g-action-full 非 g-mul 同态，
-- 见证经 c2∘c3 共轭关系（c2-c3ⁿ）显式合成，非经 g-mul 传递）
~g-refl : ∀ x → GOrbitRel x x
~g-refl (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) = g-orbit-path g-id refl

~g-sym : ∀ x y → GOrbitRel x y → GOrbitRel y x
~g-sym (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) .(g-action-full g (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []))
       (g-orbit-path g refl) = help g
  where
  step : ∀ t x → c2 (c3ⁿ t (c2 (c3ⁿ t x))) ≡ x
  step t x = trans (cong (λ z → c2 (c3ⁿ t z)) (c2-c3ⁿ t x))
              (trans (cong c2 mid) (c2-invol x))
    where
    mid : c3ⁿ t (c3ⁿ (neg3 t) (c2 x)) ≡ c2 x
    mid = trans (sym (c3ⁿ-add t (neg3 t) (c2 x)))
            (cong (λ z → c3ⁿ z (c2 x)) (+₃-negʳ t))
  help : ∀ g → GOrbitRel (g-action-full g (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []))
                          (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
  help ⟨ c3₃ a b c , zero ⟩ =
    g-orbit-path ⟨ c3₃ (neg3 a) (neg3 b) (neg3 c) , zero ⟩
      (v6 (c3ⁿ-inv a x₀) (c3ⁿ-inv b x₁) (c3ⁿ-inv c x₂) refl refl refl)
  help ⟨ c3₃ a b c , suc zero ⟩ =
    g-orbit-path ⟨ c3₃ a b c , suc zero ⟩
      (v6 (step a x₀) (step b x₁) (step c x₂) (c2-invol x₃) (c2-invol x₄) (c2-invol x₅))

~g-trans : ∀ x y z → GOrbitRel x y → GOrbitRel y z → GOrbitRel x z
~g-trans (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
         .(g-action-full g₁ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []))
         .(g-action-full g₂ (g-action-full g₁ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])))
         (g-orbit-path g₁ refl) (g-orbit-path g₂ refl) = help g₂ g₁
  where
  help : ∀ g₂ g₁ → GOrbitRel (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
        (g-action-full g₂ (g-action-full g₁ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])))
  help ⟨ c3₃ a₂ b₂ k₂ , zero ⟩ ⟨ c3₃ a₁ b₁ k₁ , zero ⟩ =
    g-orbit-path ⟨ c3₃ (a₂ +₃ a₁) (b₂ +₃ b₁) (k₂ +₃ k₁) , zero ⟩
      (v6 (c3ⁿ-add a₂ a₁ x₀) (c3ⁿ-add b₂ b₁ x₁) (c3ⁿ-add k₂ k₁ x₂) refl refl refl)
  help ⟨ c3₃ a₂ b₂ k₂ , suc zero ⟩ ⟨ c3₃ a₁ b₁ k₁ , zero ⟩ =
    g-orbit-path ⟨ c3₃ (a₂ +₃ a₁) (b₂ +₃ b₁) (k₂ +₃ k₁) , suc zero ⟩
      (v6 (cong (λ z → c2 z) (c3ⁿ-add a₂ a₁ x₀))
          (cong (λ z → c2 z) (c3ⁿ-add b₂ b₁ x₁))
          (cong (λ z → c2 z) (c3ⁿ-add k₂ k₁ x₂)) refl refl refl)
  help ⟨ c3₃ a₂ b₂ k₂ , zero ⟩ ⟨ c3₃ a₁ b₁ k₁ , suc zero ⟩ =
    g-orbit-path ⟨ c3₃ (neg3 (a₂ +₃ neg3 a₁)) (neg3 (b₂ +₃ neg3 b₁)) (neg3 (k₂ +₃ neg3 k₁)) , suc zero ⟩
      (v6 (step3 a₂ a₁ x₀) (step3 b₂ b₁ x₁) (step3 k₂ k₁ x₂) refl refl refl)
    where
    rhsD : ∀ t₂ t₁ x → c3ⁿ t₂ (c2 (c3ⁿ t₁ x)) ≡ c3ⁿ (t₂ +₃ neg3 t₁) (c2 x)
    rhsD t₂ t₁ x = trans (cong (c3ⁿ t₂) (c2-c3ⁿ t₁ x))
      (sym (c3ⁿ-add t₂ (neg3 t₁) (c2 x)))
    step3 : ∀ t₂ t₁ x → c2 (c3ⁿ (neg3 (t₂ +₃ neg3 t₁)) x) ≡ c3ⁿ t₂ (c2 (c3ⁿ t₁ x))
    step3 t₂ t₁ x = trans (c2-c3ⁿ (neg3 (t₂ +₃ neg3 t₁)) x)
      (trans (cong (λ z → c3ⁿ z (c2 x)) (neg3-invol (t₂ +₃ neg3 t₁)))
        (sym (rhsD t₂ t₁ x)))
  help ⟨ c3₃ a₂ b₂ k₂ , suc zero ⟩ ⟨ c3₃ a₁ b₁ k₁ , suc zero ⟩ =
    g-orbit-path ⟨ c3₃ (neg3 (a₂ +₃ neg3 a₁)) (neg3 (b₂ +₃ neg3 b₁)) (neg3 (k₂ +₃ neg3 k₁)) , zero ⟩
      (v6 (fin a₂ a₁ x₀) (fin b₂ b₁ x₁) (fin k₂ k₁ x₂) (sym (c2-invol x₃)) (sym (c2-invol x₄)) (sym (c2-invol x₅)))
    where
    rhs : ∀ t₂ t₁ x → c2 (c3ⁿ t₂ (c2 (c3ⁿ t₁ x))) ≡ c3ⁿ (neg3 (t₂ +₃ neg3 t₁)) x
    rhs t₂ t₁ x = trans (cong (λ z → c2 (c3ⁿ t₂ z)) (c2-c3ⁿ t₁ x))
      (trans (cong c2 (sym (c3ⁿ-add t₂ (neg3 t₁) (c2 x))))
        (trans (c2-c3ⁿ (t₂ +₃ neg3 t₁) (c2 x))
          (cong (c3ⁿ (neg3 (t₂ +₃ neg3 t₁))) (c2-invol x))))
    fin : ∀ t₂ t₁ x → c3ⁿ (neg3 (t₂ +₃ neg3 t₁)) x ≡ c2 (c3ⁿ t₂ (c2 (c3ⁿ t₁ x)))
    fin t₂ t₁ x = sym (rhs t₂ t₁ x)
