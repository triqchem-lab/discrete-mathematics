{-# OPTIONS --rewriting #-}

-- | Sovereign.Geometry.ProjectiveCore
-- 4320D 射影几何核心：规范群 G = (C₃)³ ⋊ C₂ + 射影点 = G-不可约轨道
--
-- G = (C₃ × C₃ × C₃) ⋊ C₂, |G| = 54
-- 信息 = 群轨道, 非 βη 语法等价

module Sovereign.Geometry.ProjectiveCore where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Structology.T6 using (T6Lattice)

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

g-inv : GElement → GElement
g-inv ⟨ c3₃ a b c , h ⟩ = ⟨ c3₃ (i3 a) (i3 b) (i3 c) , h ⟩
  where i3 : Fin 3 → Fin 3
        i3 zero = zero
        i3 (suc zero) = suc (suc zero)
        i3 (suc (suc zero)) = suc zero

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

-- 群公理 (声明, 待穷举证明)
postulate
  g-id-left   : ∀ g → g-mul g-id g ≡ g
  g-id-right  : ∀ g → g-mul g g-id ≡ g
  g-inv-left  : ∀ g → g-mul (g-inv g) g ≡ g-id
  g-assoc     : ∀ g h k → g-mul (g-mul g h) k ≡ g-mul g (g-mul h k)
  ~g-refl     : ∀ x → GOrbitRel x x
  ~g-sym      : ∀ x y → GOrbitRel x y → GOrbitRel y x
  ~g-trans    : ∀ x y z → GOrbitRel x y → GOrbitRel y z → GOrbitRel x z
