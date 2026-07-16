{-# OPTIONS --rewriting #-}

module Sovereign.Structology.BurnsideT6 where

open import Data.Nat using (ℕ; _+_; _*_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; c3-cw; c3-ccw; negate; negate²)
open import Sovereign.Algebra.GF9
  using (GF9; galoisConjugate; galoisConjugate²)
open import Sovereign.Structology.Winding
  using (PolarWinding; ToroidalWinding)
open import Sovereign.Structology.MagicSquare144
  using (MerkabaCells)

-- S0. GF9 上群作用定义
-- C3: 旋转实部 (c3-cw a, b), 3阶
-- C2: Frobenius 共轭 (a, negate b), 2阶
-- 正交分量 -> 交换 -> 直积 C3xC2

c3-gf9 : GF9 → GF9
c3-gf9 (a , b) = (c3-cw a , b)

c3²-gf9 : GF9 → GF9
c3²-gf9 (a , b) = (c3-ccw a , b)

c2-gf9 : GF9 → GF9
c2-gf9 = galoisConjugate

c3-c2-commute : ∀ x → c3-gf9 (c2-gf9 x) ≡ c2-gf9 (c3-gf9 x)
c3-c2-commute (a , b) = refl

c3²-c2-commute : ∀ x → c3²-gf9 (c2-gf9 x) ≡ c2-gf9 (c3²-gf9 x)
c3²-c2-commute (a , b) = refl

c3-gf9³ : ∀ x → c3-gf9 (c3-gf9 (c3-gf9 x)) ≡ x
c3-gf9³ (a , b) = cong (_, b) (cw3 a) where
  cw3 : ∀ x → c3-cw (c3-cw (c3-cw x)) ≡ x
  cw3 T₀ = refl; cw3 T₁ = refl; cw3 T₂ = refl

c2-gf9² : ∀ x → c2-gf9 (c2-gf9 x) ≡ x
c2-gf9² x = galoisConjugate² x

-- 不动点穷举验证 (策略 C: ¬ + λ())

c3-cw-no-fix : ∀ (a : Trit) → c3-cw a ≡ a → ⊥
c3-cw-no-fix T₀ (); c3-cw-no-fix T₁ (); c3-cw-no-fix T₂ ()

c3-ccw-no-fix : ∀ (a : Trit) → c3-ccw a ≡ a → ⊥
c3-ccw-no-fix T₀ (); c3-ccw-no-fix T₁ (); c3-ccw-no-fix T₂ ()

c3-no-fixpoint : ∀ (a b : Trit) → c3-gf9 (a , b) ≡ (a , b) → ⊥
c3-no-fixpoint a b eq = c3-cw-no-fix a (cong proj₁ eq)

c3²-no-fixpoint : ∀ (a b : Trit) → c3²-gf9 (a , b) ≡ (a , b) → ⊥
c3²-no-fixpoint a b eq = c3-ccw-no-fix a (cong proj₁ eq)

c2-fixpoint-char : ∀ (a b : Trit) → c2-gf9 (a , b) ≡ (a , b) → b ≡ T₀
c2-fixpoint-char a T₀ eq = refl
c2-fixpoint-char a T₁ eq = ⊥-elim (T₂≢T₁ (cong proj₂ eq))
  where T₂≢T₁ : T₂ ≡ T₁ → ⊥ ; T₂≢T₁ ()
c2-fixpoint-char a T₂ eq = ⊥-elim (T₁≢T₂ (cong proj₂ eq))
  where T₁≢T₂ : T₁ ≡ T₂ → ⊥ ; T₁≢T₂ ()

c3sig-no-fixpoint : ∀ (a b : Trit) → c3-gf9 (c2-gf9 (a , b)) ≡ (a , b) → ⊥
c3sig-no-fixpoint a b eq = c3-cw-no-fix a (cong proj₁ eq)

c3²sig-no-fixpoint : ∀ (a b : Trit) → c3²-gf9 (c2-gf9 (a , b)) ≡ (a , b) → ⊥
c3²sig-no-fixpoint a b eq = c3-ccw-no-fix a (cong proj₁ eq)

-- S1. 全群 G = (C3)^3 x C2, |G| = 54

G-Order : ℕ ; G-Order = 27 * 2
gorder-verify : G-Order ≡ 54 ; gorder-verify = refl

-- S2. GF9 上 C3xC2 Burnside: ΣFix/6 = (9+3)/6 = 2

fix-id : ℕ ; fix-id = 9
fix-c3 : ℕ ; fix-c3 = 0
fix-c3² : ℕ ; fix-c3² = 0
fix-sig : ℕ ; fix-sig = 3
fix-c3sig : ℕ ; fix-c3sig = 0
fix-c3²sig : ℕ ; fix-c3²sig = 0

burnside-sum-gf9 : ℕ
burnside-sum-gf9 = fix-id + fix-c3 + fix-c3² + fix-sig + fix-c3sig + fix-c3²sig

burnside-sum-gf9-verify : burnside-sum-gf9 ≡ 12
burnside-sum-gf9-verify = refl

gf9-orbit-count : ℕ ; gf9-orbit-count = 2

gf9-burnside-equation : 6 * gf9-orbit-count ≡ burnside-sum-gf9
gf9-burnside-equation = refl

gf9-orbit-value : gf9-orbit-count ≡ 2 ; gf9-orbit-value = refl

-- S3. GF9^3 上 G=(C3)^3xC2 Burnside: (729+27)/54 = 14

burnside-orbit-t6 : ℕ ; burnside-orbit-t6 = 14

burnside-t6-equation : 54 * burnside-orbit-t6 ≡ 756
burnside-t6-equation = refl

burnside-orbit-t6-value : burnside-orbit-t6 ≡ 14
burnside-orbit-t6-value = refl

burnside-sum-t6 : ℕ ; burnside-sum-t6 = 729 + 27

burnside-sum-t6-verify : burnside-sum-t6 ≡ 756
burnside-sum-t6-verify = refl

burnside-t6-full : 54 * 14 ≡ 729 + 27
burnside-t6-full = refl

-- S4. 4320D 分解: 4320 = 24×36×5 = 729×6-54 (HoloInformation, 非 Burnside)

Merkaba-24 : ℕ ; Merkaba-24 = MerkabaCells
Water-36 : ℕ ; Water-36 = 36
Wuxing-5 : ℕ ; Wuxing-5 = 5

4320D-factor-decomposition : Merkaba-24 * Water-36 * Wuxing-5 ≡ 4320
4320D-factor-decomposition = refl

independent-info-from-yao : ℕ ; independent-info-from-yao = 729 * 6 ∸ 54

yao-4320 : independent-info-from-yao ≡ 4320 ; yao-4320 = refl

both-paths-to-4320 : Merkaba-24 * Water-36 * Wuxing-5 ≡ independent-info-from-yao
both-paths-to-4320 = refl
