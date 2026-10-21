{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF9KernelImageZero
--
-- **`q_n = 0`**：对角算子的核与像交为零（正确环 `Functions((Z/3)^n, GF9)` 上）。
--
-- ## 数学背景
--
-- T4 的正确环是 `R_n = Functions((Z/3)^n, GF9)`（GF9-值函数环）。
-- 算子 `F = Σ_j x_j²` 是**对角算子**：`(F f) x = λ_x · f x`，其中 `λ_x = Hamming(x) mod 3`
-- （嵌入 GF9，故 `λ_x ∈ {0, 1, -1} ⊂ GF9`）。
--
-- 对角算子的核/像按**坐标集**划分：
--   · `ker F`  = 支撑在 `{x : λ_x = 0}` 上
--   · `im F`   = 支撑在 `{x : λ_x ≠ 0}` 上
-- ⇒ 两者支撑**互补** ⇒ 交为零 ⇒ **`q_n = dim(ker F ∩ im F) = 0`** ✓
--
-- ## 本模块证明的
--
-- `q-zero : Ker f → Im f → f ≡ 0`（逐点形式，无 subspaces 需求）
--
-- ## 核心原则
--   · 用**支撑论证**（逐点），不用 `Basis`/子空间层
--   · `GF9` 是**域**（无零因子）—— 由 `embed-gf3` 归约到 GF(3) 的 3 个 case
--   · 不引入 postulate / hole

module Sovereign.Algebra.LinearAlgebra.GF9KernelImageZero where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Algebra.FieldTower.GF9 using
  ( GF9; _*gf9_; gf9-zero; gf9-one; embed-gf3; embed-gf3-mul; embed-gf3-injective )
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus)

--------------------------------------------------------------------------------
-- §1. Hamming 模 3（Trit 值）
--------------------------------------------------------------------------------

-- `Fin 3` 的非零指示（0 ↦ 0，1 ↦ 1，2 ↦ 1）
nz3 : Fin 3 → Trit
nz3 fzero                 = T₀
nz3 (fsuc fzero)          = T₁
nz3 (fsuc (fsuc fzero))   = T₁

-- `hammingT x = Hamming(x) mod 3`（Trit 值，用 ⊕ 累加）
hammingT : ∀ {n} → Torus n → Trit
hammingT []       = T₀
hammingT (x ∷ xs) = nz3 x ⊕ hammingT xs

--------------------------------------------------------------------------------
-- §2. 对角算子 `F9`
--------------------------------------------------------------------------------

F9 : ℕ → Set
F9 n = Torus n → GF9

-- 对角算子：`(Fop f) x = λ_x · f x`（λ_x = embed-gf3 (hammingT x)）
Fop : ∀ {n} → F9 n → F9 n
Fop f x = embed-gf3 (hammingT x) *gf9 f x

-- 核谓词
Ker : ∀ {n} → F9 n → Set
Ker {n} f = ∀ (x : Torus n) → Fop f x ≡ gf9-zero

-- 像谓词（对角算子的像：`f = F g` 逐点）
Im : ∀ {n} → F9 n → Set
Im {n} f = ∃ (λ (g : F9 n) → ∀ (x : Torus n) → f x ≡ Fop g x)

--------------------------------------------------------------------------------
-- §3. GF9 的无零因子（只需 λ = ±1 两个 case）
--------------------------------------------------------------------------------

-- `embed-gf3 T₁ = (T₁ , T₀) = gf9-one`
e1 : embed-gf3 T₁ ≡ gf9-one
e1 = refl

-- `gf9-one * y = y`（9 case）
one-mul : ∀ (y : GF9) → gf9-one *gf9 y ≡ y
one-mul (T₀ , T₀) = refl
one-mul (T₀ , T₁) = refl
one-mul (T₀ , T₂) = refl
one-mul (T₁ , T₀) = refl
one-mul (T₁ , T₁) = refl
one-mul (T₁ , T₂) = refl
one-mul (T₂ , T₀) = refl
one-mul (T₂ , T₁) = refl
one-mul (T₂ , T₂) = refl

-- `(T₂ , T₀) * y ≡ 0 → y ≡ 0`（9 case）
t2-nzd : ∀ (y : GF9) → (T₂ , T₀) *gf9 y ≡ gf9-zero → y ≡ gf9-zero
t2-nzd (T₀ , T₀) _ = refl
t2-nzd (T₀ , T₁) ()
t2-nzd (T₀ , T₂) ()
t2-nzd (T₁ , T₀) ()
t2-nzd (T₁ , T₁) ()
t2-nzd (T₁ , T₂) ()
t2-nzd (T₂ , T₀) ()
t2-nzd (T₂ , T₁) ()
t2-nzd (T₂ , T₂) ()

--------------------------------------------------------------------------------
-- §4. ★★★ 主定理：`ker F ∩ im F = 0`（即 `q_n = 0`）
--------------------------------------------------------------------------------

-- `0 * y ≡ 0`（9 case）
zero-mul : ∀ (y : GF9) → (T₀ , T₀) *gf9 y ≡ (T₀ , T₀)
zero-mul (T₀ , T₀) = refl
zero-mul (T₀ , T₁) = refl
zero-mul (T₀ , T₂) = refl
zero-mul (T₁ , T₀) = refl
zero-mul (T₁ , T₁) = refl
zero-mul (T₁ , T₂) = refl
zero-mul (T₂ , T₀) = refl
zero-mul (T₂ , T₁) = refl
zero-mul (T₂ , T₂) = refl

-- `embed-gf3 T₀ ≡ gf9-zero`
e0 : embed-gf3 T₀ ≡ gf9-zero
e0 = refl

-- `embed-gf3 T₂ ≡ (T₂ , T₀)`
e2 : embed-gf3 T₂ ≡ (T₂ , T₀)
e2 = refl

-- ★★★ 主定理（显式等式参数，绕过 `with` 不抽象 β-归约项的问题）
q-zero-aux : ∀ {n} (f : F9 n) → Ker f → Im f → ∀ (x : Torus n) (h : Trit) →
  hammingT x ≡ h → f x ≡ gf9-zero
q-zero-aux f ker (g , im) x T₀ eq =
  trans (im x)
        (trans (cong (λ z → z *gf9 g x) (cong embed-gf3 eq))
               (zero-mul (g x)))
q-zero-aux f ker (g , im) x T₁ eq =
  trans (sym (one-mul (f x)))
        (trans (cong (λ z → z *gf9 f x) (sym (trans (cong embed-gf3 eq) e1)))
               (ker x))
q-zero-aux f ker (g , im) x T₂ eq =
  t2-nzd (f x)
    (trans (cong (λ z → z *gf9 f x) (sym (trans (cong embed-gf3 eq) e2)))
           (ker x))

-- ★★★★ `q_n = 0`：核像交为零
q-zero : ∀ {n} (f : F9 n) → Ker f → Im f → ∀ (x : Torus n) → f x ≡ gf9-zero
q-zero f ker im x = q-zero-aux f ker im x (hammingT x) refl
