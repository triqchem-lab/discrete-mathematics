{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.C3Orbit
-- C₃ 轨道定理: {1,3,5} 在 +2 (mod 6) 下构成 C₃ 群轨道。
-- 对应三分损益 Sun=+1, Yi=+2 在指数域中的生成元作用。
--
-- C₃ 作用: a_i → a_{(i+2) mod 6}
-- 轨道: 1 → 3 → 5 → 1 (周期 3)
-- 不动点: {0,2,4} (偶数项, C₃ 作用下不变 mod 6?)

module Sovereign.Algebra.C3Orbit where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- C₃ 生成元作用: +2 (mod 6)
add2-mod6 : ℕ → ℕ
add2-mod6 n = (n + 2) % 6

-- 轨道 {1,3,5} 在 C₃ 作用下封闭
orbit-step-1 : add2-mod6 1 ≡ 3
orbit-step-1 = refl  -- (1+2)%6 = 3

orbit-step-3 : add2-mod6 3 ≡ 5
orbit-step-3 = refl  -- (3+2)%6 = 5

orbit-step-5 : add2-mod6 5 ≡ 1
orbit-step-5 = refl  -- (5+2)%6 = 7%6 = 1

-- C₃ 群乘法表 (生成元 g=add2-mod6, g³=id)
C3-mult-table : Vec (Vec ℕ 3) 3
C3-mult-table = (0 ∷ 1 ∷ 2 ∷ [])  -- g⁰ = id
              ∷ (1 ∷ 2 ∷ 0 ∷ [])  -- g¹
              ∷ (2 ∷ 0 ∷ 1 ∷ [])  -- g² = g⁻¹
              ∷ []

-- 轨道定理: 轨道 {1,3,5} 的大小 = 3 (即 C₃ 群阶)
orbit-size : (1 ≡ 1) × (add2-mod6 1 ≡ 3) × (add2-mod6 (add2-mod6 1) ≡ 5) × (add2-mod6 (add2-mod6 (add2-mod6 1)) ≡ 1)
orbit-size = refl , refl , refl , refl

-- 与三分损益的对应 (Sun=+1, Yi=+2)
-- Christoffel 螺旋 mod 3 = [1,2,1,2,1,2] = Sun,Yi 交替
