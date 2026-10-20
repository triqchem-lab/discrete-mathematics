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

open import Data.Nat using (ℕ; zero; suc; _∸_; _+_; _≟_)
open import Data.Nat.Properties using (∸-+-assoc; +-comm; +-assoc; suc-injective)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus)
open import Sovereign.Algebra.LinearAlgebra.GF3Barrier using (zeroAt; lookupAt; T₁≢T₀; T₂≢T₀)

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

--------------------------------------------------------------------------------
-- §3. 非零定位：把「和/乘子非零」退到「某一项非零」
--------------------------------------------------------------------------------

open import Sovereign.Base.Trit using (_⊕_; ⊕-identityˡ)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin)
open import Sovereign.Algebra.LinearAlgebra.GF3BlockSplit using (CoeffN; sum2)
open import Sovereign.Algebra.LinearAlgebra.GF3Barrier using (mulX2)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)

-- `sumFin` 全零 ⇒ 结果为零
sumFin-zero' : ∀ {n} (f : Fin n → Trit) → (∀ i → f i ≡ T₀) → sumFin f ≡ T₀
sumFin-zero' {zero} f h = refl
sumFin-zero' {suc m} f h =
  trans (cong₂ _⊕_ (h fzero) (sumFin-zero' {m} (λ j → f (fsuc j)) (λ j → h (fsuc j))))
        (⊕-identityˡ T₀)

-- `mulX2` 非零 ⇒ 该坐标处的指数为 2，且原函数在该点非零
mulX2-nonzero : ∀ {n} (j : Fin n) (p : CoeffN n) (b : Torus n) →
  mulX2 j p b ≢ T₀ → (lookupAt j b ≡ fsuc (fsuc fzero)) × (p (zeroAt j b) ≢ T₀)
mulX2-nonzero j p b ne with lookupAt j b
... | fzero             = ⊥-elim (ne refl)
... | fsuc fzero        = ⊥-elim (ne refl)
... | fsuc (fsuc fzero) = refl , ne

--------------------------------------------------------------------------------
-- §4. ★★ `F` 升片：支撑在 `#2 = k` 的片上 ⇒ `F p` 支撑在 `#2 = k+1` 的片上
--------------------------------------------------------------------------------

Supp : ∀ {n} (P : Torus n → Set) (p : CoeffN n) → Set
Supp {n} P p = ∀ (x : Torus n) → p x ≢ T₀ → P x

-- 切片谓词
Slice : ∀ {n} → ℕ → Torus n → Set
Slice {n} k a = wt2 a ≡ k

-- ★ 核心：若 `wt2 b ≠ k+1`，则 `sum2 p b = T₀`（逆向陈述，避开「某项非零」）
sum2-zero-off-slice : ∀ {n} (p : CoeffN n) (k : ℕ) →
  Supp (Slice k) p → ∀ (b : Torus n) → wt2 b ≢ suc k → sum2 p b ≡ T₀
sum2-zero-off-slice {n} p k sp b ne =
  sumFin-zero' {n} (λ j → mulX2 j p b) goal
  where
    open import Sovereign.Algebra.LinearAlgebra.GF3Barrier using (trit-zero)

    goal : ∀ j → mulX2 j p b ≡ T₀
    goal j with lookupAt j b in eqL
    ... | fzero             = refl
    ... | fsuc fzero        = refl
    ... | fsuc (fsuc fzero) =
      trit-zero (p (zeroAt j b))
                (λ pnz → ne (trans (wt2-zeroAt-suc j b eqL)
                                   (cong suc (sp (zeroAt j b) pnz))))

-- ★★ 主定理（正向）：`F` 把 `#2 = k` 的片升到 `#2 = k+1`
sum2-slice : ∀ {n} (p : CoeffN n) (k : ℕ) →
  Supp (Slice k) p → Supp (Slice (suc k)) (sum2 p)
sum2-slice {n} p k sp b nz with wt2 b ≟ suc k
... | yes eq = eq
... | no neq = ⊥-elim (nz (sum2-zero-off-slice p k sp b neq))
