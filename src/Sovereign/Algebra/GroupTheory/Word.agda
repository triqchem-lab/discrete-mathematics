{-# OPTIONS --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.Word
-- **两个生成元上的词**（含逆字母）与其拼接——B₃ 的载体语法层。
--
-- 为什么单独成模块：
--   本件**零依赖**（不 import Trit、不 import 任何 --rewriting 模块）。
--   于是 `--cubical` 的商模块可以只导入本件 + `BraidCongruence`，
--   导入锥内**没有任何 REWRITE 规则**——不会触发「cubical 静默丢弃规则」这个坑
--   （探针实测：`--rewriting --cubical` 可编译，但真规则被忽略，`refl` 失败）。
--
-- 表示选择：snoc-列表（`_++W_` 递归在**第二元**）。
--   代价：任何「插入」操作都必须前插（见 BraidCongruence 的 pre* 系列）。
--   收益：`w ++W [x]` 恰是「右接一个字母」，与构造子一一对应，判等与归纳都直。
--
-- 包含：Word / ε / 四个字母构造子 / _++W_ / ++W-assoc / ++W-idˡ / ++W-idʳ / aba / bab
-- 0 postulate / 0 hole。

module Sovereign.Algebra.GroupTheory.Word where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

infixl 20 _·a
infixl 20 _·b
infixl 20 _·ai
infixl 20 _·bi

data Word : Set where
  ε   : Word
  _·a  : Word → Word    -- 右接 σ₁
  _·b  : Word → Word    -- 右接 σ₂
  _·ai : Word → Word    -- 右接 σ₁⁻¹
  _·bi : Word → Word    -- 右接 σ₂⁻¹

-- 词拼接：递归在第二元（snoc 列表）
_++W_ : Word → Word → Word
p ++W ε       = p
p ++W (q ·a)  = (p ++W q) ·a
p ++W (q ·b)  = (p ++W q) ·b
p ++W (q ·ai) = (p ++W q) ·ai
p ++W (q ·bi) = (p ++W q) ·bi

-- 拼接的幺半群律（`≡` 级）
++W-assoc : ∀ (p q r : Word) → ((p ++W q) ++W r) ≡ (p ++W (q ++W r))
++W-assoc p q ε       = refl
++W-assoc p q (r ·a)  = cong (_·a) (++W-assoc p q r)
++W-assoc p q (r ·b)  = cong (_·b) (++W-assoc p q r)
++W-assoc p q (r ·ai) = cong (_·ai) (++W-assoc p q r)
++W-assoc p q (r ·bi) = cong (_·bi) (++W-assoc p q r)

++W-idˡ : ∀ (p : Word) → (ε ++W p) ≡ p
++W-idˡ ε       = refl
++W-idˡ (p ·a)  = cong (_·a) (++W-idˡ p)
++W-idˡ (p ·b)  = cong (_·b) (++W-idˡ p)
++W-idˡ (p ·ai) = cong (_·ai) (++W-idˡ p)
++W-idˡ (p ·bi) = cong (_·bi) (++W-idˡ p)

++W-idʳ : ∀ (p : Word) → (p ++W ε) ≡ p
++W-idʳ p = refl

-- B₃ 的定义关系的两个词：σ₁σ₂σ₁ 与 σ₂σ₁σ₂
aba : Word
aba = ((ε ·a) ·b) ·a

bab : Word
bab = ((ε ·b) ·a) ·b
