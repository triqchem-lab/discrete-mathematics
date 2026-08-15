{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.DifferenceEq
-- 34/39 ODE/差分补强 — Fibonacci 递推 mod 3 的周期 8 轨道 (0 postulate)
--
-- y(n+2) = y(n+1) + y(n) (mod 3): 0,1,1,2,0,2,2,1,0,1,... — 周期 8

module Sovereign.Analysis.DifferenceEq where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)

-- 状态 (y(n), y(n+1)) — 递推步: (a,b) ↦ (b, a⊕b)
step : Trit × Trit → Trit × Trit
step (a , b) = (b , (a ⊕ b))

-- 周期表: 8 步循环 (0,1) → (1,1) → (1,2) → (2,0) → (0,2) → (2,2) → (2,1) → (1,0) → (0,1)
fib-1 : step (T₀ , T₁) ≡ (T₁ , T₁) ; fib-1 = refl
fib-2 : step (step (T₀ , T₁)) ≡ (T₁ , T₂) ; fib-2 = refl
fib-3 : step (step (step (T₀ , T₁))) ≡ (T₂ , T₀) ; fib-3 = refl
fib-4 : step (step (step (step (T₀ , T₁)))) ≡ (T₀ , T₂) ; fib-4 = refl
fib-5 : step (step (step (step (step (T₀ , T₁))))) ≡ (T₂ , T₂) ; fib-5 = refl
fib-6 : step (step (step (step (step (step (T₀ , T₁)))))) ≡ (T₂ , T₁) ; fib-6 = refl
fib-7 : step (step (step (step (step (step (step (T₀ , T₁))))))) ≡ (T₁ , T₀) ; fib-7 = refl

-- 周期 8 闭合: step⁸ (0,1) = (0,1)
fib-period-8 : step (step (step (step (step (step (step (step (T₀ , T₁)))))))) ≡ (T₀ , T₁)
fib-period-8 = refl

-- 0 postulate.
