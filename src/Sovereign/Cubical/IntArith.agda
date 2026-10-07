{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Cubical.IntArith
-- Cubical ℤ 算术补丁引理（减法与加法重排）
--
-- 核心原则：
--   1. 减法重排 ≠ negDistrib（等式里没有负号）
--   2. 4 条独立引理组合，不写 subst 链
--   3. 纯字母名避开 +pos 解析冲突
--
-- 包含：sucPush, pos-+pos, sucℤ-minus, minus-assoc, minus-shift

module Sovereign.Cubical.IntArith where

open import Cubical.Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-zero; +-suc)
open import Cubical.Data.Int using (ℤ; _+_; _-_; pos; negsuc; sucℤ; _+pos_)
open import Cubical.Data.Int.Properties using (+Comm; +Assoc; minusPlus; plusMinus; -Cancel; -Cancel'; neg+; -pos; -neg; predℤ+negsuc; predℤ+pos; -predℤ)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_; Σ; _,_; fst; snd)

-- ────────────────────────────────────────────────────────────────────
-- sucPush : sucℤ (x + y) ≡ sucℤ x + y（sucℤ 对加法的分配）
-- 用 sucInt renaming 避开 sucℤ+ 解析冲突
-- ────────────────────────────────────────────────────────────────────

sucInt : ∀ x y → sucℤ (x + y) ≡ sucℤ x + y
sucInt x y = {!!}  -- PENDING: 需 sucℤ+ 但有解析冲突

sucPush : ∀ x y → sucℤ (x + y) ≡ sucℤ x + y
sucPush x y = sucInt x y

-- ────────────────────────────────────────────────────────────────────
-- pos-+pos : pos a +pos b ≡ pos (a +ℕ b)
-- ────────────────────────────────────────────────────────────────────

pos-+pos : ∀ (a b : ℕ) → _+pos_ (pos a) b ≡ pos (a +ℕ b)
pos-+pos a zero = cong pos (sym (+-zero a))
pos-+pos a (suc b) = cong sucℤ (pos-+pos a b) ∙ cong pos (sym (+-suc a b))

-- ────────────────────────────────────────────────────────────────────
-- negDistrib : -(x + y) ≡ -x + -y（用 neg+ 组合）
-- ────────────────────────────────────────────────────────────────────

negDistrib : ∀ x y → Cubical.Data.Int.-_ (x + y) ≡ Cubical.Data.Int.-_ x + Cubical.Data.Int.-_ y
negDistrib (pos a) (pos b) = cong Cubical.Data.Int.-_ (pos-+pos a b) ∙ -pos (a +ℕ b) ∙ neg+ a b ∙ cong₂ _+_ (sym (-pos a)) (sym (-pos b))
negDistrib (pos a) (negsuc b) = {!!}  -- PENDING: pos+negsuc 展开
negDistrib (negsuc a) (pos b) = {!!}
negDistrib (negsuc a) (negsuc b) with b
... | zero = refl
... | suc b' = {!!}

-- ────────────────────────────────────────────────────────────────────
-- sucℤ-minus : sucℤ (x - y) ≡ sucℤ x - y（sucℤ 对减法的分配）
-- ────────────────────────────────────────────────────────────────────

sucℤ-minus : ∀ x y → sucℤ (x - y) ≡ sucℤ x - y
sucℤ-minus x y = sucPush x (Cubical.Data.Int.-_ y)

-- ────────────────────────────────────────────────────────────────────
-- minus-assoc : x - (y + z) ≡ (x - y) - z（减法结合）
-- ────────────────────────────────────────────────────────────────────

minus-assoc : ∀ x y z → x - (y + z) ≡ (x - y) - z
minus-assoc x y z = cong (x +_) (negDistrib y z) ∙ +Assoc x (Cubical.Data.Int.-_ y) (Cubical.Data.Int.-_ z)

-- ────────────────────────────────────────────────────────────────────
-- minus-shift : (x - y) + z ≡ (x + z) - y（减法与加法交换）
-- ────────────────────────────────────────────────────────────────────

minus-shift : ∀ x y z → (x - y) + z ≡ (x + z) - y
minus-shift x y z = sym (+Assoc x (Cubical.Data.Int.-_ y) z) ∙ cong (x +_) (+Comm (Cubical.Data.Int.-_ y) z) ∙ +Assoc x z (Cubical.Data.Int.-_ y)
