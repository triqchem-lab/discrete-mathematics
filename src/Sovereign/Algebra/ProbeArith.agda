{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Algebra.ProbeArith where

open import Cubical.Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-zero; +-suc)
open import Cubical.Data.Int using (ℤ; _+_; _-_; pos; negsuc; sucℤ; _+pos_; _*_; neg)
open import Cubical.Data.Int.Order using (_<_; _≤_; ≤-+o; ≤-o+; ≤-+o-cancel; isTrans≤; isRefl≤)
open import Cubical.Data.Int.Properties using (+Comm; +Assoc; +sucℤ; minusPlus; plusMinus; -Cancel) renaming (sucℤ+ to sucInt)
open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; subst; Σ; _,_; fst; snd; _∙_; funExt)

-- 核心消去引理（参照 mathlib4 le.elim）：
-- a ≤ b 可以消去为「存在 ℕ 见证 k 使得 a +pos k ≡ b」
-- 这正是 Cubical 的 < / ≤ 的定义形式，现在把它封装为可直接用的工具

-- 序到等式消去：< 的见证是 Σ ℕ，直接取分量
<-witness : {a b : ℤ} → a < b → ℕ
<-witness (k , _) = k

<-eq : {a b : ℤ} → (h : a < b) → sucℤ a +pos <-witness h ≡ b
<-eq (_ , p) = p

-- ≤ 的见证
≤-witness : {a b : ℤ} → a ≤ b → ℕ
≤-witness (k , _) = k

≤-eq : {a b : ℤ} → (h : a ≤ b) → a +pos ≤-witness h ≡ b
≤-eq (_ , p) = p

-- 关键引理：n < Lf + Lg → Lf ≤ k → n - k < Lg
-- 用 ≤-eq 消去为算术等式后用 cong/transport 组合
-- sucIntPlus: sucℤ (x + y) ≡ sucℤ x + y（纯字母名避开解析冲突）
sucPush : ∀ x y → sucℤ (x + y) ≡ sucℤ x + y
sucPush x y = sucInt x y

pos-+pos : ∀ (a b : ℕ) → _+pos_ (pos a) b ≡ pos (a +ℕ b)
pos-+pos a zero = cong pos (sym (+-zero a))
pos-+pos a (suc b) = cong sucℤ (pos-+pos a b) ∙ cong pos (sym (+-suc a b))

probe : (n Lf Lg k : ℤ) → n < Lf + Lg → Lf ≤ k → n - k < Lg
probe n Lf Lg k (a , p₁) (b , p₂) = (a +ℕ b) , lem
  where
  lem : sucℤ (n - k) +pos (a +ℕ b) ≡ Lg
  lem = subst (λ x → sucℤ (n - x) +pos (a +ℕ b) ≡ Lg) p₂ lem'
    where
    lem' : sucℤ (n - (Lf +pos b)) +pos (a +ℕ b) ≡ Lg
    lem' = subst (λ x → sucℤ (n - (Lf +pos b)) +pos (a +ℕ b) ≡ x - Lf) p₁ lem'' ∙ cong (_- Lf) (+Comm Lf Lg) ∙ plusMinus Lf Lg
      where
      lem'' : sucℤ (n - (Lf +pos b)) +pos (a +ℕ b) ≡ (sucℤ n +pos a) - Lf
      lem'' = {!!}  -- PENDING: pos-+pos 类型待修 + 全限定 -_ 冗长
