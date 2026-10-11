{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.NumberTheory.Primes
-- 数学背景：素数、合数、分解串——算术基本定理的载体。
--   本模块给出 **IsPrime 关系形**（关系入定义：2≤p + 无真因子为字段非公理），
--   与 stdlib `Data.Nat.Primality`（Prime/notComposite 形）对标互涵（立界注记）；
--   分解存在性/唯一性为深定理——**如实立界**（实例分解层已证）。
-- 核心原则：
-- 1. 复用优先：stdlib Primality 对标基座；∣ 句法复用 Divisibility 族
-- 2. 0 postulate / 0 hole
-- 3. 关系入定义（IsPrime/IsComposite/Factorization）
-- 4. 实例核对层与通用定义层分层（六段式）
-- 包含：IsPrime · IsComposite · Factorization · isPrime-2 · isPrime-3 · 实例 ×4

module Sovereign.Algebra.NumberTheory.Primes where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.Properties using (1+n≰n; ≤-trans; ≤-antisym; ≤-pred)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- §1 定义层：IsPrime / IsComposite / Factorization（关系入定义）
--------------------------------------------------------------------------------

-- IsPrime p：p ≥ 2 且 [2,p) 内无因子
record IsPrime (p : ℕ) : Set where
  field
    2≤p        : 2 ≤ p
    no-divisor : ∀ d → 2 ≤ d → d < p → (d ∣ p) → ⊥

-- IsComposite n：真分解 n = a * b（a,b ≥ 2）
IsComposite : ℕ → Set
IsComposite n = Σ ℕ λ a → Σ ℕ λ b → Σ (2 ≤ a) λ _ → Σ (2 ≤ b) λ _ → a * b ≡ n

-- Factorization：素因子串（分解存在性的实例承载）
data Factorization : ℕ → Set where
  one  : Factorization 1
  cons : ∀ p → IsPrime p → ∀ m → Factorization m → Factorization (p * m)

--------------------------------------------------------------------------------
-- §2 主引理层：最小素数
--------------------------------------------------------------------------------

-- isPrime-2：区间 [2,2) 空——因子前提自矛盾
isPrime-2 : IsPrime 2
isPrime-2 = record { 2≤p = s≤s (s≤s z≤n) ; no-divisor = no-div-2 }
  where
  no-div-2 : ∀ d → 2 ≤ d → d < 2 → (d ∣ 2) → ⊥
  no-div-2 d 2≤d d<2 _ = 1+n≰n (≤-trans d<2 2≤d)

-- isPrime-3：区间 [2,3) 唯一候选 d=2；2∤3 经商形消解
isPrime-3 : IsPrime 3
isPrime-3 = record { 2≤p = s≤s (s≤s z≤n) ; no-divisor = no-div-3 }
  where
  3≢0 : 3 ≡ 0 → ⊥
  3≢0 ()

  3≢2 : 3 ≡ 2 → ⊥
  3≢2 ()

  3≢4+ : ∀ r → 3 ≡ 2 + (2 + r * 2) → ⊥
  3≢4+ r ()

  go : ∀ {d} → 2 ≡ d → ∀ q → 3 ≡ q * d → ⊥
  go refl zero    eq = 3≢0 eq
  go refl (suc zero) eq = 3≢2 eq
  go refl (suc (suc r)) eq = 3≢4+ r eq

  no-div-3 : ∀ d → 2 ≤ d → d < 3 → (d ∣ 3) → ⊥
  no-div-3 d 2≤d d<3 (divides q eq) =
    go (≤-antisym 2≤d (≤-pred d<3)) q eq

--------------------------------------------------------------------------------
-- §3 组合层：合数与分解实例
--------------------------------------------------------------------------------

-- composite-4：4 = 2 × 2
composite-4 : IsComposite 4
composite-4 = 2 , 2 , s≤s (s≤s z≤n) , s≤s (s≤s z≤n) , refl

-- composite-6：6 = 2 × 3
composite-6 : IsComposite 6
composite-6 = 2 , 3 , s≤s (s≤s z≤n) , s≤s (s≤s z≤n) , refl

-- fact-12：12 = 2 × 6 = 2 × 2 × 3（分解串实例）
fact-6 : Factorization 6
fact-6 = cons 2 isPrime-2 3 (cons 3 isPrime-3 1 one)

fact-12 : Factorization 12
fact-12 = cons 2 isPrime-2 6 fact-6

--------------------------------------------------------------------------------
-- §4 核对层与立界
--------------------------------------------------------------------------------

-- 对标注记：stdlib `Data.Nat.Primality.Pride`（notComposite 形）↔ IsPrime 互涵桥
--   （Prime → IsPrime 需 Composite record 面对表；IsPrime → Prime 需 ¬Composite 提取）——立界注记。
-- 立界（如实）：① 分解存在性（∀ n ≥ 2 → Σ Factorization——归纳构造）；
--   ② 唯一性（重排等价——算术基本定理本体）；③ 筛正确性（sieve 面）。
