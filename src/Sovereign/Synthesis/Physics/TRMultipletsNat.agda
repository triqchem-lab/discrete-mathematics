{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Physics.TRMultipletsNat
--
-- TR 维数恒等式的**完整形式**（ℕ 索引）：
--     sumOdd a n + a² ≡ (a+n)²,   sumOdd a n = Σ_{i<n} (2(a+i)+1)
-- 取 a = |l−J|、n = 2·min(l,J)+1 即得 Σ_λ (2λ+1) = (2l+1)(2J+1)。
--
-- 代数核心在 ℤ 上（`TRMultipletsZ.sq-suc-Z`，RingSolver）；本模块补 ℕ→ℤ 的 cast 管道。
--
-- 0 postulate / 0 hole。
module Sovereign.Synthesis.Physics.TRMultipletsNat where

open import Data.Nat using (ℕ; zero; suc)
open import Agda.Builtin.Nat using () renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties as ℕP using ()
open import Data.Integer using (ℤ; +_; +0; _+_; _*_; -_)
open import Data.Integer.Properties using (+-assoc; +-identityʳ; +-identityˡ; +-inverseʳ; pos-+; pos-*)
open import Data.Integer.Tactic.RingSolver using (solve-∀)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import Sovereign.Synthesis.Physics.TRMultipletsZ using (sq-suc-Z)

--------------------------------------------------------------------------------
-- §1. 连续奇数和（ℕ 索引，ℤ 值）
--------------------------------------------------------------------------------
sumOdd : ℤ → ℕ → ℤ
sumOdd a zero = +0
sumOdd a (suc n) = sumOdd a n + ((+ 2) * (a + + n) + (+ 1))

--------------------------------------------------------------------------------
-- §2. cast 管道
--------------------------------------------------------------------------------
suc-eq-N : ∀ n → suc n ≡ n +ℕ 1
suc-eq-N n = sym (trans (ℕP.+-suc n 0) (cong suc (ℕP.+-identityʳ n)))

pos-suc : ∀ n → + (suc n) ≡ (+ n) + (+ 1)
pos-suc n = cong +_ (suc-eq-N n)

--------------------------------------------------------------------------------
-- §3. 重排（交给 ring solver）
--------------------------------------------------------------------------------
rearr : ∀ (S X A : ℤ) → (S + X) + A ≡ (S + A) + X
rearr = solve-∀

--------------------------------------------------------------------------------
-- §4. 主定理
--------------------------------------------------------------------------------
sum-odd : ∀ (a : ℤ) (n : ℕ) → sumOdd a n + a * a ≡ (a + + n) * (a + + n)
sum-odd a zero = begin
    sumOdd a 0 + a * a
  ≡⟨ refl ⟩
    +0 + a * a
  ≡⟨ +-identityˡ (a * a) ⟩
    a * a
  ≡⟨ sym (cong₂ _*_ (+-identityʳ a) (+-identityʳ a)) ⟩
    (a + +0) * (a + +0)
  ∎
  where
    open ≡-Reasoning
sum-odd a (suc n) = begin
    sumOdd a (suc n) + a * a
  ≡⟨ refl ⟩
    (sumOdd a n + ((+ 2) * (a + + n) + (+ 1))) + a * a
  ≡⟨ rearr (sumOdd a n) ((+ 2) * (a + + n) + (+ 1)) (a * a) ⟩
    (sumOdd a n + a * a) + ((+ 2) * (a + + n) + (+ 1))
  ≡⟨ cong (λ z → z + ((+ 2) * (a + + n) + (+ 1))) (sum-odd a n) ⟩
    (a + + n) * (a + + n) + ((+ 2) * (a + + n) + (+ 1))
  ≡⟨ sq-suc-Z (a + + n) ⟩
    ((a + + n) + (+ 1)) * ((a + + n) + (+ 1))
  ≡⟨ cong₂ _*_ eq eq ⟩
    (a + + (suc n)) * (a + + (suc n))
  ∎
  where
    open ≡-Reasoning
    eq : (a + + n) + (+ 1) ≡ a + + (suc n)
    eq = trans (+-assoc a (+ n) (+ 1)) (cong (λ z → a + z) (sym (pos-suc n)))


--------------------------------------------------------------------------------
-- §5. 实例核验：λ 从 |l−J| 到 l+J 的连续奇数和 = (2l+1)(2J+1)
--     （取 a = J ∸ l（l ≤ J）、n = 2l+1；此处直接给数值实例，全部 refl）
--------------------------------------------------------------------------------
-- l = 1, J = 1：λ = 0,1,2 → 1+3+5 = 9 = 3×3
tr-l1-J1 : sumOdd (+ 0) 3 ≡ + 9
tr-l1-J1 = refl

-- l = 2, J = 2：λ = 0..4 → 1+3+5+7+9 = 25 = 5×5
tr-l2-J2 : sumOdd (+ 0) 5 ≡ + 25
tr-l2-J2 = refl

-- l = 2, J = 3：a = 1, n = 5 → 3+5+7+9+11 = 35 = 5×7
tr-l2-J3 : sumOdd (+ 1) 5 ≡ + 35
tr-l2-J3 = refl

-- l = 3, J = 3：λ = 0..6 → 49 = 7×7
tr-l3-J3 : sumOdd (+ 0) 7 ≡ + 49
tr-l3-J3 = refl
