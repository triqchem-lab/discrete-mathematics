{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.RootMath.Base
-- 根数学 GF(3) 基础件：Trit 编码与运算
--
-- 核心原则：
--   1. Trit ↔ ℕ 编码互逆（encodeDecodeInverse）+ GF(3) 加法 _+ᵍᶠ_；
--   2. 根数学自有基件（与 Base/Trit 平行的独立小世界）。
-- 包含：data Trit、tritToℕ、tritEncode、tritDecode、encodeDecodeInverse、tritEq、_+ᵍᶠ_、gf3Zero
module Sovereign.RootMath.Base where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_)
open import Data.Nat.DivMod using (_div_; _%_; m%n<n)
open import Data.Nat.Properties using (≤-trans; <⇒≤; +-mono-≤; ≤-pred)
open import Data.Bool using (Bool; true; false; T)
open import Data.Integer using (ℤ; +_; -[1+_]; _-_; _*_) renaming (_+_ to _+ℤ_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

data Trit : Set where
  T₀ : Trit
  T₁ : Trit
  T₂ : Trit

tritToℕ : Trit → ℕ
tritToℕ T₀ = 0
tritToℕ T₁ = 1
tritToℕ T₂ = 2

tritEncode : Trit → Fin 3
tritEncode T₀ = zero
tritEncode T₁ = suc zero
tritEncode T₂ = suc (suc zero)

tritDecode : Fin 3 → Trit
tritDecode zero = T₀
tritDecode (suc zero) = T₁
tritDecode (suc (suc zero)) = T₂

encodeDecodeInverse : ∀ (t : Trit) → tritDecode (tritEncode t) ≡ t
encodeDecodeInverse T₀ = refl
encodeDecodeInverse T₁ = refl
encodeDecodeInverse T₂ = refl

tritEq : (t₁ t₂ : Trit) → Bool
tritEq T₀ T₀ = true
tritEq T₁ T₁ = true
tritEq T₂ T₂ = true
tritEq _  _  = false

_+ᵍᶠ_ : Trit → Trit → Trit
T₀ +ᵍᶠ x = x
x +ᵍᶠ T₀ = x
T₁ +ᵍᶠ T₁ = T₂
T₁ +ᵍᶠ T₂ = T₀
T₂ +ᵍᶠ T₁ = T₀
T₂ +ᵍᶠ T₂ = T₁

gf3Zero : Trit
gf3Zero = T₀

gf3Neg : Trit → Trit
gf3Neg T₀ = T₀
gf3Neg T₁ = T₂
gf3Neg T₂ = T₁

gf3NegCancel : ∀ (x : Trit) → x +ᵍᶠ gf3Neg x ≡ gf3Zero
gf3NegCancel T₀ = refl
gf3NegCancel T₁ = refl
gf3NegCancel T₂ = refl

Tryte : Set
Tryte = Vec Trit 6

tryteToℕ⁶ : Tryte → Vec ℕ 6
tryteToℕ⁶ = map tritToℕ

zeroTryte : Tryte
zeroTryte = T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₀ ∷ []

-- 数字根：O(1) 公式
digitalRoot : ℕ → ℕ
digitalRoot 0 = 0
digitalRoot n@(suc _) = 1 + ((n ∸ 1) % 9)

-- 数字根 ≤ 9 的证明
digitalRoot≤9 : ∀ n → digitalRoot n ≤ 9
digitalRoot≤9 zero = Data.Nat.z≤n
digitalRoot≤9 n@(suc _) =
  let rem<9 : (n ∸ 1) % 9 < 9
      rem<9 = m%n<n (n ∸ 1) 9
      rem≤8 : (n ∸ 1) % 9 ≤ 8
      rem≤8 = ≤-pred rem<9
  in Data.Nat.s≤s rem≤8

data StableDigitalRoot : ℕ → Set where
  root3 : StableDigitalRoot 3
  root6 : StableDigitalRoot 6
  root9 : StableDigitalRoot 9

isStableRoot : ℕ → Bool
isStableRoot 3 = true
isStableRoot 6 = true
isStableRoot 9 = true
isStableRoot _ = false

IsStable : ℕ → Bool
IsStable n = isStableRoot n

-- [分类: 已证引理] [状态: 核心四极框架]
-- 核心引理：数字根 ∈ {3,6,9} 时, 构造 StableDigitalRoot 证明。
-- 【构造化 2026-10-11】原 postulate 病因 = 对 stuck 项 digitalRoot n 直接匹配（wildcard 不规约）；
--   正解 = 辅助件泛化到任意 m + 具体值分支（豁免精化判据「符号/具体值拆分」正解①）。
--   ⚠ 尾部必须 suc¹¹ 起（suc⁴ 尾会盖住 6/9——m=2/5 时 suc⁴m=6/9，case tree 拒归约是对的）。
stableRootAux : (m : ℕ) → T (isStableRoot m) → StableDigitalRoot m
stableRootAux zero ()
stableRootAux 1 ()
stableRootAux 2 ()
stableRootAux 3 _ = root3
stableRootAux 4 ()
stableRootAux 5 ()
stableRootAux 6 _ = root6
stableRootAux 7 ()
stableRootAux 8 ()
stableRootAux 9 _ = root9
stableRootAux 10 ()
stableRootAux (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))) ()

stableRootConstraint : ∀ {n} → T (IsStable (digitalRoot n)) → StableDigitalRoot (digitalRoot n)
stableRootConstraint {n} w = stableRootAux (digitalRoot n) w
