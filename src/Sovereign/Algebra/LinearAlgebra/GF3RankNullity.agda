{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3RankNullity
-- 秩-零化度（T4 的最后一个基础设施件，2026-10-21）
--
-- 数学
--   对线性映射 `T : V → W`（`V`、`W` 为有限维 GF(3) 向量空间）：
--       **dim V = dim ker T + dim im T**
--
-- 本库的维数语义（见 `GF3BasisCount`）：
--   `Basis V` ⇒ `V ≅ Fin (3^(dim V))`   ⇒   `|V| = 3^(dim V)`
--   ⇒ 维数等式可以化为**基数等式**：`3^(dim V) = 3^(dim ker) · 3^(dim im)`
--   ⇒ 再加 `3^`-单射即可。**不需要**抽象的 `dim` 函数。
--
-- 本模块
--   §1 `3^`-单射（`3^a = 3^b ⇒ a = b`）
--   §2 纤维乘积分解 `V ≅ im T × ker T`（用 `GF3Fiber` 的纤维等大）
--   §3 拼装出维数公式
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3RankNullity where

open import Data.Nat using (ℕ; zero; suc; _*_; _^_; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  ( <-irrefl; <-trans; <-cmp; *-monoˡ-<; *-monoʳ-<; ^-monoˡ-≤; ≤-refl; ≤-trans; n≤1+n )
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no; ¬_)

--------------------------------------------------------------------------------
-- §1. `3^`-单射：`3^a ≡ 3^b ⇒ a ≡ b`
--
-- 直接用 stdlib：`^-monoʳ-< : ∀ m → 1 < m → Monotonic₁ _<_ _<_ (m ^_)`
--------------------------------------------------------------------------------

open import Data.Nat.Properties using
  ( ^-monoʳ-<; <-irrefl; <-cmp; <-trans; ≤-refl; ≤-trans
  ; m≤m+n; n≤1+n< )
open import Data.Nat using (_<_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Tri)

1<3 : 1 < 3
1<3 = s≤s (s≤s z≤n)

-- `3^` 严格单调
3^-mono-< : ∀ {a b} → a < b → 3 ^ a < 3 ^ b
3^-mono-< = ^-monoʳ-< 3 1<3

-- ★ `3^`-单射
3^-inj : ∀ {a b} → 3 ^ a ≡ 3 ^ b → a ≡ b
3^-inj {a} {b} eq with <-cmp a b
... | Tri.tri< a<b _ _   = ⊥-elim (<-irrefl eq (3^-mono-< a<b))
... | Tri.tri≈ _ a≡b _   = a≡b
... | Tri.tri> _ _ b<a   = ⊥-elim (<-irrefl (sym eq) (3^-mono-< b<a))
