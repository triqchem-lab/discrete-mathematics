{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3Barrier
-- 系数表示下的**壁垒定理**准备工作（T4，2026-10-20）
--
-- 数学内容
--   `CoeffN n = Torus n → Trit` 是**系数函数**：`p a` = 单项式 `x^a` 的系数。
--   乘 `x_i²` 在系数表示下是**索引回退**：`(x_i²·p)(b) = p(b 的第 i 坐标减 2)`，
--   越界（第 i 坐标 < 2）时为 0 ⇒ **截断自动** ✓
--
-- 壁垒（人类给出的纯组合证明）
--   若 `p ≠ 0` 且 `p b ≠ 0 ⇒ b_i = 0`（支撑避开坐标 i），则 `Σ_j x_j²·p ≠ 0`。
--   证：取 `a` 使 `p a ≠ 0` ⇒ `a_i = 0` ⇒ 在 `twoAt i a` 处只有 `j = i` 项存活，
--       其值 = `p a ≠ 0` ✓
--
-- 本模块现状（诚实标注）
--   ✅ §1 系数表示 · §2 坐标改写 · §3 关键引理 `zeroAt-twoAt`
--   ⬜ §4 乘 `x_i²` 与壁垒本体 —— **未完成**（`with` 阻断定义展开，需重构为
--      `Maybe` 版 `subAt`；已在 `memory/` 记录难点）
--
-- 依赖: Sovereign.Algebra.LinearAlgebra.GF3LaplacianN（Torus）
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3Barrier where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus)

--------------------------------------------------------------------------------
-- §1. 系数表示
--------------------------------------------------------------------------------

CoeffN : ℕ → Set
CoeffN n = Torus n → Trit

f0 f2 : Fin 3
f0 = fzero
f2 = fsuc (fsuc fzero)

--------------------------------------------------------------------------------
-- §2. 坐标改写（第 i 坐标设为 T₀ / T₂）
--------------------------------------------------------------------------------

zeroAt : ∀ {n} → Fin n → Torus n → Torus n
zeroAt {n = suc n} fzero     (_ ∷ xs) = f0 ∷ xs
zeroAt {n = suc n} (fsuc i)  (x ∷ xs) = x  ∷ zeroAt i xs

twoAt : ∀ {n} → Fin n → Torus n → Torus n
twoAt {n = suc n} fzero     (_ ∷ xs) = f2 ∷ xs
twoAt {n = suc n} (fsuc i)  (x ∷ xs) = x  ∷ twoAt i xs

lookupAt : ∀ {n} → Fin n → Torus n → Fin 3
lookupAt {n = suc n} fzero     (x ∷ _)  = x
lookupAt {n = suc n} (fsuc i)  (_ ∷ xs) = lookupAt i xs

--------------------------------------------------------------------------------
-- §3. 关键引理：先设 T₂ 再设 T₀ 复原（当原值为 T₀）
--------------------------------------------------------------------------------

zeroAt-twoAt : ∀ {n} (i : Fin n) (a : Torus n) →
  lookupAt i a ≡ f0 → zeroAt i (twoAt i a) ≡ a
zeroAt-twoAt {n = suc n} fzero     (x ∷ xs) eq = cong₂ _∷_ (sym eq) refl
zeroAt-twoAt {n = suc n} (fsuc i)  (x ∷ xs) eq =
  cong₂ _∷_ refl (zeroAt-twoAt i xs eq)

--------------------------------------------------------------------------------
-- §4. 乘 `x_i²`：用 Maybe 避开 with（关键：`mulX2` 内**不能有 with**）
--------------------------------------------------------------------------------

open import Data.Maybe using (Maybe; just; nothing; maybe)

-- 索引回退：第 i 坐标减 2；不足 2 时 nothing（⇒ 截断自动）
subAt : ∀ {n} → Fin n → Torus n → Maybe (Torus n)
subAt {n = suc n} fzero (x ∷ xs) with x
... | fzero          = nothing
... | fsuc fzero     = nothing
... | fsuc (fsuc _)  = just (f0 ∷ xs)
subAt {n = suc n} (fsuc i) (x ∷ xs) =
  maybe (λ ys → just (x ∷ ys)) nothing (subAt i xs)

mulX2 : ∀ {n} → Fin n → CoeffN n → CoeffN n
mulX2 i p b = maybe p T₀ (subAt i b)

-- ★ `twoAt i a` 的第 i 坐标是 T₂ ⇒ `subAt` 解回 `zeroAt i (twoAt i a)`
subAt-twoAt : ∀ {n} (i : Fin n) (a : Torus n) →
  subAt i (twoAt i a) ≡ just (zeroAt i (twoAt i a))
subAt-twoAt {n = suc n} fzero (a ∷ as) = refl
subAt-twoAt {n = suc n} (fsuc i) (a ∷ as) =
  trans (cong (maybe (λ ys → just (a ∷ ys)) nothing) (subAt-twoAt i as)) refl

-- 乘 `x_i²` 在 `twoAt` 处解回 `p`
mulX2-twoAt : ∀ {n} (i : Fin n) (p : CoeffN n) (a : Torus n) →
  mulX2 i p (twoAt i a) ≡ p (zeroAt i (twoAt i a))
mulX2-twoAt i p a = cong (maybe p T₀) (subAt-twoAt i a)

-- `twoAt i a` 的第 i 坐标是 T₂
lookupAt-twoAt : ∀ {n} (i : Fin n) (a : Torus n) → lookupAt i (twoAt i a) ≡ f2
lookupAt-twoAt {n = suc n} fzero (a ∷ as) = refl
lookupAt-twoAt {n = suc n} (fsuc i) (a ∷ as) = lookupAt-twoAt i as

-- `j ≠ i` 时 `zeroAt j (twoAt i a)` 的第 i 坐标仍是 T₂
lookupAt-zeroAt-other : ∀ {n} (i j : Fin n) → i ≢ j → (a : Torus n) →
  lookupAt i (zeroAt j (twoAt i a)) ≡ f2
lookupAt-zeroAt-other {n = suc n} fzero fzero ne (a ∷ as) = ⊥-elim (ne refl)
lookupAt-zeroAt-other {n = suc n} fzero (fsuc j) ne (a ∷ as) = refl
lookupAt-zeroAt-other {n = suc n} (fsuc i) fzero ne (a ∷ as) = lookupAt-twoAt i as
lookupAt-zeroAt-other {n = suc n} (fsuc i) (fsuc j) ne (a ∷ as) =
  lookupAt-zeroAt-other i j (λ e → ne (cong fsuc e)) as
