{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Problem.PvsNP.jac_Complexity3 where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

record M3 : Set where
  field c00 c01 c02 : Trit
  field c10 c11 c12 : Trit
  field c20 c21 c22 : Trit

negate : Trit → Trit; negate T₀ = T₀; negate T₁ = T₂; negate T₂ = T₁

det3 : M3 → Trit
det3 m =
  let a0 = (M3.c00 m ⊗ M3.c11 m) ⊗ M3.c22 m
      a1 = (M3.c01 m ⊗ M3.c12 m) ⊗ M3.c20 m
      a2 = (M3.c02 m ⊗ M3.c10 m) ⊗ M3.c21 m
      b0 = (M3.c02 m ⊗ M3.c11 m) ⊗ M3.c20 m
      b1 = (M3.c01 m ⊗ M3.c10 m) ⊗ M3.c22 m
      b2 = (M3.c00 m ⊗ M3.c12 m) ⊗ M3.c21 m
  in ((a0 ⊕ a1) ⊕ a2) ⊕ (negate ((b0 ⊕ b1) ⊕ b2))

diag-det : det3 (record { c00 = T₁ ; c01 = T₀ ; c02 = T₀ ; c10 = T₀ ; c11 = T₂ ; c12 = T₀ ; c20 = T₀ ; c21 = T₀ ; c22 = T₁ }) ≡ T₂
diag-det = refl

-- companion matrix for λ³+2λ+1 (irreducible over GF(3))
CM : M3
CM = record { c00 = T₀ ; c01 = T₀ ; c02 = T₂
            ; c10 = T₁ ; c11 = T₀ ; c12 = T₁
            ; c20 = T₀ ; c21 = T₁ ; c22 = T₀ }

det-CM : det3 CM ≡ T₂; det-CM = refl              -- det=2

-- §2. 不可约判定: charPoly(λ)=λ³+aλ²+bλ+c
-- CM: trace=0 → a=T₀. det=2 → c=T₁. 主2×2子式和 → b=T₂.
-- charPoly = λ³ + 0·λ² + 2·λ + 1 = λ³ + 2λ + 1 (GF(3))
-- 根测试: GF(3) 仅 {0,1,2}, 代入验证非零即不可约.

-- 求值: f(λ) = λ³ + 2·λ + 1
f₃ : Trit → Trit
f₃ x = (((x ⊗ x) ⊗ x) ⊕ (T₂ ⊗ x)) ⊕ T₁

-- f(0)=1, f(1)=4≡1, f(2)=13≡1 (mod 3)
f0-val : f₃ T₀ ≡ T₁; f0-val = refl
f1-val : f₃ T₁ ≡ T₁; f1-val = refl
f2-val : f₃ T₂ ≡ T₁; f2-val = refl

-- 不可约: 三个求值全非零 → 没有 GF(3) 根 → 不可约
-- T₁ ≢ T₀ 由构造子差异直接成立 (λ()).
irr-CM-f0 : T₁ ≢ T₀; irr-CM-f0 = λ ()
irr-CM-f1 : T₁ ≢ T₀; irr-CM-f1 = λ ()
irr-CM-f2 : T₁ ≢ T₀; irr-CM-f2 = λ ()
