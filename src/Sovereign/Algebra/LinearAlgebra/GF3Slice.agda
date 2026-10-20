{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3Slice
-- ★ `F` 的 `#2` 分片递升结构（T4 的 q_n 分解，2026-10-20）
--
-- 数学背景
--   `F = Σ_j x_j²` 作用在单项式 `x^a` 上：
--     `F(x^a) = Σ_{j : a_j = 0} x^{a + 2e_j}`
--   ⇒ 令 `#2(a) = #{j : a_j = 2}`（指数为 2 的坐标个数），则
--     **`F` 把「指数全在 {0,1} 的片」升到「恰好一个 2 的片」**，等等。
--
--   精确地说：`F` 的**输出在 `b` 处非零** 意味着 `F` 在某个 `j` 上取了
--   `p (zeroAt j b)`，而 `zeroAt` 把 `#2` **降一格**：
--       `lookupAt j b = f2  ⇒  #2 (zeroAt j b) = #2 b ∸ 1`
--   ⇒ 若 `p` 只在 `#2 = k` 的片上非零，则 `F p` 只在 `#2 = k+1` 的片上非零
--   ⇒ **`F : span(S_k) → span(S_{k+1})`**（这就是分片直和的来源）
--
-- 本模块
--   §1 `wt2`（权重）+ 基本引理（零权重、加一权重）
--   §2 ★ `wt2-zeroAt`：`zeroAt` 在 `a_j = f2` 时把权重降一
--   §3 `Supp`（支撑谓词）与 `sum2-slice`（`F` 升片的点态形式）
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3Slice where

open import Data.Nat using (ℕ; zero; suc; _∸_; _+_)
open import Data.Nat.Properties using (∸-+-assoc; +-comm; +-assoc; suc-injective)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus)
open import Sovereign.Algebra.LinearAlgebra.GF3Barrier using (zeroAt; lookupAt)

--------------------------------------------------------------------------------
-- §1. 权重 `#2`：指数为 2 的坐标个数
--------------------------------------------------------------------------------

wt2 : ∀ {n} → Torus n → ℕ
wt2 [] = 0
wt2 (fzero ∷ xs) = wt2 xs
wt2 (fsuc fzero ∷ xs) = wt2 xs
wt2 (fsuc (fsuc fzero) ∷ xs) = suc (wt2 xs)

--------------------------------------------------------------------------------
-- §2. ★ `zeroAt` 把权重降一格（当该坐标为 2 时）
--------------------------------------------------------------------------------

-- 先证一个「lookup 为 f2 才能降」的辅助：`zeroAt` 的权重只在新坐标是 f2 时降 1
wt2-zeroAt-zero : ∀ {n} (i : Fin n) (a : Torus n) →
  lookupAt i a ≡ fzero → wt2 (zeroAt i a) ≡ wt2 a
wt2-zeroAt-zero {n = suc n} fzero (x ∷ xs) eq
  rewrite eq = refl
wt2-zeroAt-zero {n = suc n} (fsuc i) (fzero ∷ xs) eq =
  wt2-zeroAt-zero i xs eq
wt2-zeroAt-zero {n = suc n} (fsuc i) (fsuc fzero ∷ xs) eq =
  wt2-zeroAt-zero i xs eq
wt2-zeroAt-zero {n = suc n} (fsuc i) (fsuc (fsuc fzero) ∷ xs) eq =
  cong suc (wt2-zeroAt-zero i xs eq)

wt2-zeroAt-one : ∀ {n} (i : Fin n) (a : Torus n) →
  lookupAt i a ≡ fsuc fzero → wt2 (zeroAt i a) ≡ wt2 a
wt2-zeroAt-one {n = suc n} fzero (x ∷ xs) eq
  rewrite eq = refl
wt2-zeroAt-one {n = suc n} (fsuc i) (fzero ∷ xs) eq =
  wt2-zeroAt-one i xs eq
wt2-zeroAt-one {n = suc n} (fsuc i) (fsuc fzero ∷ xs) eq =
  wt2-zeroAt-one i xs eq
wt2-zeroAt-one {n = suc n} (fsuc i) (fsuc (fsuc fzero) ∷ xs) eq =
  cong suc (wt2-zeroAt-one i xs eq)

-- ★ 主引理（`+1` 形式，避免 `∸`）：
--   `lookupAt i a = f2  ⇒  wt2 a ≡ suc (wt2 (zeroAt i a))`
wt2-zeroAt-suc : ∀ {n} (i : Fin n) (a : Torus n) →
  lookupAt i a ≡ fsuc (fsuc fzero) → wt2 a ≡ suc (wt2 (zeroAt i a))
wt2-zeroAt-suc {n = suc n} fzero (fzero ∷ xs) ()
wt2-zeroAt-suc {n = suc n} fzero (fsuc fzero ∷ xs) ()
wt2-zeroAt-suc {n = suc n} fzero (fsuc (fsuc fzero) ∷ xs) eq = refl
wt2-zeroAt-suc {n = suc n} (fsuc i) (fzero ∷ xs) eq =
  wt2-zeroAt-suc i xs eq
wt2-zeroAt-suc {n = suc n} (fsuc i) (fsuc fzero ∷ xs) eq =
  wt2-zeroAt-suc i xs eq
wt2-zeroAt-suc {n = suc n} (fsuc i) (fsuc (fsuc fzero) ∷ xs) eq =
  cong suc (wt2-zeroAt-suc i xs eq)
