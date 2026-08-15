{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DivisorLattice
-- 06 序与格理论补强 — 12 的除数格 (分配格 + Möbius) (0 postulate)
--
-- Div12 = {(a,b) | 0≤a≤2, 0≤b≤1} = 2^a·3^b — 6 元素
-- meet = 逐分量 min, join = 逐分量 max — 链 C3×C2 的乘积格 (分配格)

module Sovereign.Algebra.DivisorLattice where

open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

-- Fin 3 的 min/max (9 项表)
min3 : Fin 3 → Fin 3 → Fin 3
min3 fz _ = fz
min3 (fs fz) fz = fz
min3 (fs fz) (fs _) = fs fz
min3 (fs (fs fz)) fz = fz
min3 (fs (fs fz)) (fs fz) = fs fz
min3 (fs (fs fz)) (fs (fs fz)) = fs (fs fz)

max3 : Fin 3 → Fin 3 → Fin 3
max3 fz y = y
max3 (fs fz) fz = fs fz
max3 (fs fz) (fs fz) = fs fz
max3 (fs fz) (fs (fs fz)) = fs (fs fz)
max3 (fs (fs fz)) _ = fs (fs fz)

-- Fin 2 的 min/max (4 项表)
min2 : Fin 2 → Fin 2 → Fin 2
min2 fz _ = fz
min2 (fs fz) y = y

max2 : Fin 2 → Fin 2 → Fin 2
max2 fz y = y
max2 (fs fz) _ = fs fz

Div12 : Set
Div12 = Fin 3 × Fin 2

meet : Div12 → Div12 → Div12
meet (a , b) (c , d) = min3 a c , min2 b d

join : Div12 → Div12 → Div12
join (a , b) (c , d) = max3 a c , max2 b d
min3-comm : ∀ x y → min3 x y ≡ min3 y x
min3-comm fz fz = refl
min3-comm fz (fs fz) = refl
min3-comm fz (fs (fs fz)) = refl
min3-comm (fs fz) fz = refl
min3-comm (fs fz) (fs fz) = refl
min3-comm (fs fz) (fs (fs fz)) = refl
min3-comm (fs (fs fz)) fz = refl
min3-comm (fs (fs fz)) (fs fz) = refl
min3-comm (fs (fs fz)) (fs (fs fz)) = refl
max3-comm : ∀ x y → max3 x y ≡ max3 y x
max3-comm fz fz = refl
max3-comm fz (fs fz) = refl
max3-comm fz (fs (fs fz)) = refl
max3-comm (fs fz) fz = refl
max3-comm (fs fz) (fs fz) = refl
max3-comm (fs fz) (fs (fs fz)) = refl
max3-comm (fs (fs fz)) fz = refl
max3-comm (fs (fs fz)) (fs fz) = refl
max3-comm (fs (fs fz)) (fs (fs fz)) = refl
min3-idem : ∀ x → min3 x x ≡ x
min3-idem fz = refl
min3-idem (fs fz) = refl
min3-idem (fs (fs fz)) = refl
max3-idem : ∀ x → max3 x x ≡ x
max3-idem fz = refl
max3-idem (fs fz) = refl
max3-idem (fs (fs fz)) = refl
min3-assoc : ∀ x y z → min3 (min3 x y) z ≡ min3 x (min3 y z)
min3-assoc fz fz fz = refl
min3-assoc fz fz (fs fz) = refl
min3-assoc fz fz (fs (fs fz)) = refl
min3-assoc fz (fs fz) fz = refl
min3-assoc fz (fs fz) (fs fz) = refl
min3-assoc fz (fs fz) (fs (fs fz)) = refl
min3-assoc fz (fs (fs fz)) fz = refl
min3-assoc fz (fs (fs fz)) (fs fz) = refl
min3-assoc fz (fs (fs fz)) (fs (fs fz)) = refl
min3-assoc (fs fz) fz fz = refl
min3-assoc (fs fz) fz (fs fz) = refl
min3-assoc (fs fz) fz (fs (fs fz)) = refl
min3-assoc (fs fz) (fs fz) fz = refl
min3-assoc (fs fz) (fs fz) (fs fz) = refl
min3-assoc (fs fz) (fs fz) (fs (fs fz)) = refl
min3-assoc (fs fz) (fs (fs fz)) fz = refl
min3-assoc (fs fz) (fs (fs fz)) (fs fz) = refl
min3-assoc (fs fz) (fs (fs fz)) (fs (fs fz)) = refl
min3-assoc (fs (fs fz)) fz fz = refl
min3-assoc (fs (fs fz)) fz (fs fz) = refl
min3-assoc (fs (fs fz)) fz (fs (fs fz)) = refl
min3-assoc (fs (fs fz)) (fs fz) fz = refl
min3-assoc (fs (fs fz)) (fs fz) (fs fz) = refl
min3-assoc (fs (fs fz)) (fs fz) (fs (fs fz)) = refl
min3-assoc (fs (fs fz)) (fs (fs fz)) fz = refl
min3-assoc (fs (fs fz)) (fs (fs fz)) (fs fz) = refl
min3-assoc (fs (fs fz)) (fs (fs fz)) (fs (fs fz)) = refl
max3-assoc : ∀ x y z → max3 (max3 x y) z ≡ max3 x (max3 y z)
max3-assoc fz fz fz = refl
max3-assoc fz fz (fs fz) = refl
max3-assoc fz fz (fs (fs fz)) = refl
max3-assoc fz (fs fz) fz = refl
max3-assoc fz (fs fz) (fs fz) = refl
max3-assoc fz (fs fz) (fs (fs fz)) = refl
max3-assoc fz (fs (fs fz)) fz = refl
max3-assoc fz (fs (fs fz)) (fs fz) = refl
max3-assoc fz (fs (fs fz)) (fs (fs fz)) = refl
max3-assoc (fs fz) fz fz = refl
max3-assoc (fs fz) fz (fs fz) = refl
max3-assoc (fs fz) fz (fs (fs fz)) = refl
max3-assoc (fs fz) (fs fz) fz = refl
max3-assoc (fs fz) (fs fz) (fs fz) = refl
max3-assoc (fs fz) (fs fz) (fs (fs fz)) = refl
max3-assoc (fs fz) (fs (fs fz)) fz = refl
max3-assoc (fs fz) (fs (fs fz)) (fs fz) = refl
max3-assoc (fs fz) (fs (fs fz)) (fs (fs fz)) = refl
max3-assoc (fs (fs fz)) fz fz = refl
max3-assoc (fs (fs fz)) fz (fs fz) = refl
max3-assoc (fs (fs fz)) fz (fs (fs fz)) = refl
max3-assoc (fs (fs fz)) (fs fz) fz = refl
max3-assoc (fs (fs fz)) (fs fz) (fs fz) = refl
max3-assoc (fs (fs fz)) (fs fz) (fs (fs fz)) = refl
max3-assoc (fs (fs fz)) (fs (fs fz)) fz = refl
max3-assoc (fs (fs fz)) (fs (fs fz)) (fs fz) = refl
max3-assoc (fs (fs fz)) (fs (fs fz)) (fs (fs fz)) = refl
min3-max3-absorb : ∀ x y → min3 x (max3 x y) ≡ x
min3-max3-absorb fz fz = refl
min3-max3-absorb fz (fs fz) = refl
min3-max3-absorb fz (fs (fs fz)) = refl
min3-max3-absorb (fs fz) fz = refl
min3-max3-absorb (fs fz) (fs fz) = refl
min3-max3-absorb (fs fz) (fs (fs fz)) = refl
min3-max3-absorb (fs (fs fz)) fz = refl
min3-max3-absorb (fs (fs fz)) (fs fz) = refl
min3-max3-absorb (fs (fs fz)) (fs (fs fz)) = refl
max3-min3-absorb : ∀ x y → max3 x (min3 x y) ≡ x
max3-min3-absorb fz fz = refl
max3-min3-absorb fz (fs fz) = refl
max3-min3-absorb fz (fs (fs fz)) = refl
max3-min3-absorb (fs fz) fz = refl
max3-min3-absorb (fs fz) (fs fz) = refl
max3-min3-absorb (fs fz) (fs (fs fz)) = refl
max3-min3-absorb (fs (fs fz)) fz = refl
max3-min3-absorb (fs (fs fz)) (fs fz) = refl
max3-min3-absorb (fs (fs fz)) (fs (fs fz)) = refl
min3-max3-distrib : ∀ x y z → min3 x (max3 y z) ≡ max3 (min3 x y) (min3 x z)
min3-max3-distrib fz fz fz = refl
min3-max3-distrib fz fz (fs fz) = refl
min3-max3-distrib fz fz (fs (fs fz)) = refl
min3-max3-distrib fz (fs fz) fz = refl
min3-max3-distrib fz (fs fz) (fs fz) = refl
min3-max3-distrib fz (fs fz) (fs (fs fz)) = refl
min3-max3-distrib fz (fs (fs fz)) fz = refl
min3-max3-distrib fz (fs (fs fz)) (fs fz) = refl
min3-max3-distrib fz (fs (fs fz)) (fs (fs fz)) = refl
min3-max3-distrib (fs fz) fz fz = refl
min3-max3-distrib (fs fz) fz (fs fz) = refl
min3-max3-distrib (fs fz) fz (fs (fs fz)) = refl
min3-max3-distrib (fs fz) (fs fz) fz = refl
min3-max3-distrib (fs fz) (fs fz) (fs fz) = refl
min3-max3-distrib (fs fz) (fs fz) (fs (fs fz)) = refl
min3-max3-distrib (fs fz) (fs (fs fz)) fz = refl
min3-max3-distrib (fs fz) (fs (fs fz)) (fs fz) = refl
min3-max3-distrib (fs fz) (fs (fs fz)) (fs (fs fz)) = refl
min3-max3-distrib (fs (fs fz)) fz fz = refl
min3-max3-distrib (fs (fs fz)) fz (fs fz) = refl
min3-max3-distrib (fs (fs fz)) fz (fs (fs fz)) = refl
min3-max3-distrib (fs (fs fz)) (fs fz) fz = refl
min3-max3-distrib (fs (fs fz)) (fs fz) (fs fz) = refl
min3-max3-distrib (fs (fs fz)) (fs fz) (fs (fs fz)) = refl
min3-max3-distrib (fs (fs fz)) (fs (fs fz)) fz = refl
min3-max3-distrib (fs (fs fz)) (fs (fs fz)) (fs fz) = refl
min3-max3-distrib (fs (fs fz)) (fs (fs fz)) (fs (fs fz)) = refl
min2-comm : ∀ x y → min2 x y ≡ min2 y x
min2-comm fz fz = refl
min2-comm fz (fs fz) = refl
min2-comm (fs fz) fz = refl
min2-comm (fs fz) (fs fz) = refl
max2-comm : ∀ x y → max2 x y ≡ max2 y x
max2-comm fz fz = refl
max2-comm fz (fs fz) = refl
max2-comm (fs fz) fz = refl
max2-comm (fs fz) (fs fz) = refl
min2-idem : ∀ x → min2 x x ≡ x
min2-idem fz = refl
min2-idem (fs fz) = refl
max2-idem : ∀ x → max2 x x ≡ x
max2-idem fz = refl
max2-idem (fs fz) = refl
min2-assoc : ∀ x y z → min2 (min2 x y) z ≡ min2 x (min2 y z)
min2-assoc fz fz fz = refl
min2-assoc fz fz (fs fz) = refl
min2-assoc fz (fs fz) fz = refl
min2-assoc fz (fs fz) (fs fz) = refl
min2-assoc (fs fz) fz fz = refl
min2-assoc (fs fz) fz (fs fz) = refl
min2-assoc (fs fz) (fs fz) fz = refl
min2-assoc (fs fz) (fs fz) (fs fz) = refl
max2-assoc : ∀ x y z → max2 (max2 x y) z ≡ max2 x (max2 y z)
max2-assoc fz fz fz = refl
max2-assoc fz fz (fs fz) = refl
max2-assoc fz (fs fz) fz = refl
max2-assoc fz (fs fz) (fs fz) = refl
max2-assoc (fs fz) fz fz = refl
max2-assoc (fs fz) fz (fs fz) = refl
max2-assoc (fs fz) (fs fz) fz = refl
max2-assoc (fs fz) (fs fz) (fs fz) = refl
min2-max2-absorb : ∀ x y → min2 x (max2 x y) ≡ x
min2-max2-absorb fz fz = refl
min2-max2-absorb fz (fs fz) = refl
min2-max2-absorb (fs fz) fz = refl
min2-max2-absorb (fs fz) (fs fz) = refl
max2-min2-absorb : ∀ x y → max2 x (min2 x y) ≡ x
max2-min2-absorb fz fz = refl
max2-min2-absorb fz (fs fz) = refl
max2-min2-absorb (fs fz) fz = refl
max2-min2-absorb (fs fz) (fs fz) = refl

-- Div12 格律 (分量提升 — 分配格 C3×C2)
meet-comm : ∀ x y → meet x y ≡ meet y x
meet-comm (fz , fz) (fz , fz) = refl
meet-comm (fz , fz) (fz , fs fz) = refl
meet-comm (fz , fz) (fs fz , fz) = refl
meet-comm (fz , fz) (fs fz , fs fz) = refl
meet-comm (fz , fz) (fs (fs fz) , fz) = refl
meet-comm (fz , fz) (fs (fs fz) , fs fz) = refl
meet-comm (fz , fs fz) (fz , fz) = refl
meet-comm (fz , fs fz) (fz , fs fz) = refl
meet-comm (fz , fs fz) (fs fz , fz) = refl
meet-comm (fz , fs fz) (fs fz , fs fz) = refl
meet-comm (fz , fs fz) (fs (fs fz) , fz) = refl
meet-comm (fz , fs fz) (fs (fs fz) , fs fz) = refl
meet-comm (fs fz , fz) (fz , fz) = refl
meet-comm (fs fz , fz) (fz , fs fz) = refl
meet-comm (fs fz , fz) (fs fz , fz) = refl
meet-comm (fs fz , fz) (fs fz , fs fz) = refl
meet-comm (fs fz , fz) (fs (fs fz) , fz) = refl
meet-comm (fs fz , fz) (fs (fs fz) , fs fz) = refl
meet-comm (fs fz , fs fz) (fz , fz) = refl
meet-comm (fs fz , fs fz) (fz , fs fz) = refl
meet-comm (fs fz , fs fz) (fs fz , fz) = refl
meet-comm (fs fz , fs fz) (fs fz , fs fz) = refl
meet-comm (fs fz , fs fz) (fs (fs fz) , fz) = refl
meet-comm (fs fz , fs fz) (fs (fs fz) , fs fz) = refl
meet-comm (fs (fs fz) , fz) (fz , fz) = refl
meet-comm (fs (fs fz) , fz) (fz , fs fz) = refl
meet-comm (fs (fs fz) , fz) (fs fz , fz) = refl
meet-comm (fs (fs fz) , fz) (fs fz , fs fz) = refl
meet-comm (fs (fs fz) , fz) (fs (fs fz) , fz) = refl
meet-comm (fs (fs fz) , fz) (fs (fs fz) , fs fz) = refl
meet-comm (fs (fs fz) , fs fz) (fz , fz) = refl
meet-comm (fs (fs fz) , fs fz) (fz , fs fz) = refl
meet-comm (fs (fs fz) , fs fz) (fs fz , fz) = refl
meet-comm (fs (fs fz) , fs fz) (fs fz , fs fz) = refl
meet-comm (fs (fs fz) , fs fz) (fs (fs fz) , fz) = refl
meet-comm (fs (fs fz) , fs fz) (fs (fs fz) , fs fz) = refl
join-comm : ∀ x y → join x y ≡ join y x
join-comm (fz , fz) (fz , fz) = refl
join-comm (fz , fz) (fz , fs fz) = refl
join-comm (fz , fz) (fs fz , fz) = refl
join-comm (fz , fz) (fs fz , fs fz) = refl
join-comm (fz , fz) (fs (fs fz) , fz) = refl
join-comm (fz , fz) (fs (fs fz) , fs fz) = refl
join-comm (fz , fs fz) (fz , fz) = refl
join-comm (fz , fs fz) (fz , fs fz) = refl
join-comm (fz , fs fz) (fs fz , fz) = refl
join-comm (fz , fs fz) (fs fz , fs fz) = refl
join-comm (fz , fs fz) (fs (fs fz) , fz) = refl
join-comm (fz , fs fz) (fs (fs fz) , fs fz) = refl
join-comm (fs fz , fz) (fz , fz) = refl
join-comm (fs fz , fz) (fz , fs fz) = refl
join-comm (fs fz , fz) (fs fz , fz) = refl
join-comm (fs fz , fz) (fs fz , fs fz) = refl
join-comm (fs fz , fz) (fs (fs fz) , fz) = refl
join-comm (fs fz , fz) (fs (fs fz) , fs fz) = refl
join-comm (fs fz , fs fz) (fz , fz) = refl
join-comm (fs fz , fs fz) (fz , fs fz) = refl
join-comm (fs fz , fs fz) (fs fz , fz) = refl
join-comm (fs fz , fs fz) (fs fz , fs fz) = refl
join-comm (fs fz , fs fz) (fs (fs fz) , fz) = refl
join-comm (fs fz , fs fz) (fs (fs fz) , fs fz) = refl
join-comm (fs (fs fz) , fz) (fz , fz) = refl
join-comm (fs (fs fz) , fz) (fz , fs fz) = refl
join-comm (fs (fs fz) , fz) (fs fz , fz) = refl
join-comm (fs (fs fz) , fz) (fs fz , fs fz) = refl
join-comm (fs (fs fz) , fz) (fs (fs fz) , fz) = refl
join-comm (fs (fs fz) , fz) (fs (fs fz) , fs fz) = refl
join-comm (fs (fs fz) , fs fz) (fz , fz) = refl
join-comm (fs (fs fz) , fs fz) (fz , fs fz) = refl
join-comm (fs (fs fz) , fs fz) (fs fz , fz) = refl
join-comm (fs (fs fz) , fs fz) (fs fz , fs fz) = refl
join-comm (fs (fs fz) , fs fz) (fs (fs fz) , fz) = refl
join-comm (fs (fs fz) , fs fz) (fs (fs fz) , fs fz) = refl
meet-idem : ∀ x → meet x x ≡ x
meet-idem (fz , fz) = refl
meet-idem (fz , fs fz) = refl
meet-idem (fs fz , fz) = refl
meet-idem (fs fz , fs fz) = refl
meet-idem (fs (fs fz) , fz) = refl
meet-idem (fs (fs fz) , fs fz) = refl
join-idem : ∀ x → join x x ≡ x
join-idem (fz , fz) = refl
join-idem (fz , fs fz) = refl
join-idem (fs fz , fz) = refl
join-idem (fs fz , fs fz) = refl
join-idem (fs (fs fz) , fz) = refl
join-idem (fs (fs fz) , fs fz) = refl
meet-absorb : ∀ x y → meet x (join x y) ≡ x
meet-absorb (fz , fz) (fz , fz) = refl
meet-absorb (fz , fz) (fz , fs fz) = refl
meet-absorb (fz , fz) (fs fz , fz) = refl
meet-absorb (fz , fz) (fs fz , fs fz) = refl
meet-absorb (fz , fz) (fs (fs fz) , fz) = refl
meet-absorb (fz , fz) (fs (fs fz) , fs fz) = refl
meet-absorb (fz , fs fz) (fz , fz) = refl
meet-absorb (fz , fs fz) (fz , fs fz) = refl
meet-absorb (fz , fs fz) (fs fz , fz) = refl
meet-absorb (fz , fs fz) (fs fz , fs fz) = refl
meet-absorb (fz , fs fz) (fs (fs fz) , fz) = refl
meet-absorb (fz , fs fz) (fs (fs fz) , fs fz) = refl
meet-absorb (fs fz , fz) (fz , fz) = refl
meet-absorb (fs fz , fz) (fz , fs fz) = refl
meet-absorb (fs fz , fz) (fs fz , fz) = refl
meet-absorb (fs fz , fz) (fs fz , fs fz) = refl
meet-absorb (fs fz , fz) (fs (fs fz) , fz) = refl
meet-absorb (fs fz , fz) (fs (fs fz) , fs fz) = refl
meet-absorb (fs fz , fs fz) (fz , fz) = refl
meet-absorb (fs fz , fs fz) (fz , fs fz) = refl
meet-absorb (fs fz , fs fz) (fs fz , fz) = refl
meet-absorb (fs fz , fs fz) (fs fz , fs fz) = refl
meet-absorb (fs fz , fs fz) (fs (fs fz) , fz) = refl
meet-absorb (fs fz , fs fz) (fs (fs fz) , fs fz) = refl
meet-absorb (fs (fs fz) , fz) (fz , fz) = refl
meet-absorb (fs (fs fz) , fz) (fz , fs fz) = refl
meet-absorb (fs (fs fz) , fz) (fs fz , fz) = refl
meet-absorb (fs (fs fz) , fz) (fs fz , fs fz) = refl
meet-absorb (fs (fs fz) , fz) (fs (fs fz) , fz) = refl
meet-absorb (fs (fs fz) , fz) (fs (fs fz) , fs fz) = refl
meet-absorb (fs (fs fz) , fs fz) (fz , fz) = refl
meet-absorb (fs (fs fz) , fs fz) (fz , fs fz) = refl
meet-absorb (fs (fs fz) , fs fz) (fs fz , fz) = refl
meet-absorb (fs (fs fz) , fs fz) (fs fz , fs fz) = refl
meet-absorb (fs (fs fz) , fs fz) (fs (fs fz) , fz) = refl
meet-absorb (fs (fs fz) , fs fz) (fs (fs fz) , fs fz) = refl
join-absorb : ∀ x y → join x (meet x y) ≡ x
join-absorb (fz , fz) (fz , fz) = refl
join-absorb (fz , fz) (fz , fs fz) = refl
join-absorb (fz , fz) (fs fz , fz) = refl
join-absorb (fz , fz) (fs fz , fs fz) = refl
join-absorb (fz , fz) (fs (fs fz) , fz) = refl
join-absorb (fz , fz) (fs (fs fz) , fs fz) = refl
join-absorb (fz , fs fz) (fz , fz) = refl
join-absorb (fz , fs fz) (fz , fs fz) = refl
join-absorb (fz , fs fz) (fs fz , fz) = refl
join-absorb (fz , fs fz) (fs fz , fs fz) = refl
join-absorb (fz , fs fz) (fs (fs fz) , fz) = refl
join-absorb (fz , fs fz) (fs (fs fz) , fs fz) = refl
join-absorb (fs fz , fz) (fz , fz) = refl
join-absorb (fs fz , fz) (fz , fs fz) = refl
join-absorb (fs fz , fz) (fs fz , fz) = refl
join-absorb (fs fz , fz) (fs fz , fs fz) = refl
join-absorb (fs fz , fz) (fs (fs fz) , fz) = refl
join-absorb (fs fz , fz) (fs (fs fz) , fs fz) = refl
join-absorb (fs fz , fs fz) (fz , fz) = refl
join-absorb (fs fz , fs fz) (fz , fs fz) = refl
join-absorb (fs fz , fs fz) (fs fz , fz) = refl
join-absorb (fs fz , fs fz) (fs fz , fs fz) = refl
join-absorb (fs fz , fs fz) (fs (fs fz) , fz) = refl
join-absorb (fs fz , fs fz) (fs (fs fz) , fs fz) = refl
join-absorb (fs (fs fz) , fz) (fz , fz) = refl
join-absorb (fs (fs fz) , fz) (fz , fs fz) = refl
join-absorb (fs (fs fz) , fz) (fs fz , fz) = refl
join-absorb (fs (fs fz) , fz) (fs fz , fs fz) = refl
join-absorb (fs (fs fz) , fz) (fs (fs fz) , fz) = refl
join-absorb (fs (fs fz) , fz) (fs (fs fz) , fs fz) = refl
join-absorb (fs (fs fz) , fs fz) (fz , fz) = refl
join-absorb (fs (fs fz) , fs fz) (fz , fs fz) = refl
join-absorb (fs (fs fz) , fs fz) (fs fz , fz) = refl
join-absorb (fs (fs fz) , fs fz) (fs fz , fs fz) = refl
join-absorb (fs (fs fz) , fs fz) (fs (fs fz) , fz) = refl
join-absorb (fs (fs fz) , fs fz) (fs (fs fz) , fs fz) = refl

-- Möbius 函数 (12 的除数格): μ(1)=1, μ(2)=−1, μ(3)=−1, μ(4)=0, μ(6)=1, μ(12)=0
-- 表示: Div12 → ℤ
-- (需要 Data.Integer — 单独声明)
-- 0 postulate.
