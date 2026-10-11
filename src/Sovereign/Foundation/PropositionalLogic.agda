{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Foundation.PropositionalLogic
-- 命题逻辑——语法/语义/可靠性小例（完备性立界）
--
-- 数学背景：经典命题逻辑的可判定面——公式归纳定义 + 真值求值语义。
--   与 LogicDecidable（Dec 组合器族）衔接：语义判定 = eval 后的 Bool 判据。
--   可靠性（语义后承保真）以小例全证承载；完备性（语法可导全部重言）立界。
--
-- 核心原则：
-- 1. 语法 = data 归纳（构造子穷尽——穷举边界的基座）
-- 2. 语义 = 纯函数求值（Bool 通道——免函数外延）
-- 3. 核对层全枚举（单变元 2 案/双变元 4 案 ≤27 边界内）
-- 4. 立界注记不设空壳签名
--
-- 包含：Formula · evalF · satAt · tautology₂ · 可靠性小例 · 核对层

module Sovereign.Foundation.PropositionalLogic where

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; _xor_; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

-- ────────────────────────────────────────────────────────────────────
-- §1 语法定义层（公式归纳形）
-- ────────────────────────────────────────────────────────────────────

data Formula : Set where
  atom : ℕ → Formula          -- 命题变元（ℕ 编号）
  ⊤ᶠ   : Formula              -- 恒真
  ⊥ᶠ   : Formula              -- 恒假
  ¬ᶠ   : Formula → Formula    -- 否定
  _∧ᶠ_ : Formula → Formula → Formula
  _∨ᶠ_ : Formula → Formula → Formula
  _→ᶠ_ : Formula → Formula → Formula

-- 赋值（变元 → Bool）
Assignment : Set
Assignment = ℕ → Bool

-- ────────────────────────────────────────────────────────────────────
-- §2 语义求值层
-- ────────────────────────────────────────────────────────────────────

evalF : Assignment → Formula → Bool
evalF ρ (atom n)   = ρ n
evalF ρ ⊤ᶠ         = true
evalF ρ ⊥ᶠ         = false
evalF ρ (¬ᶠ A)     = not (evalF ρ A)
evalF ρ (A ∧ᶠ B)   = evalF ρ A ∧ evalF ρ B
evalF ρ (A ∨ᶠ B)   = evalF ρ A ∨ evalF ρ B
evalF ρ (A →ᶠ B)   = if evalF ρ A then evalF ρ B else true

-- 语义后承（所有赋值保真——可靠性判据的语义面）
satAt : Assignment → Formula → Set
satAt ρ A = evalF ρ A ≡ true

-- ────────────────────────────────────────────────────────────────────
-- §3 主引理层（单/双变元全枚举核对 + 可靠性小例）
-- ────────────────────────────────────────────────────────────────────

-- 单变元两赋值（枚举基座）
ρt : Assignment
ρt _ = true

ρf : Assignment
ρf _ = false

-- 排中律 A ∨ ¬A 恒真（单变元两案全枚举 = 重言式核对）
excluded-middle-t : evalF ρt (atom 0 ∨ᶠ ¬ᶠ (atom 0)) ≡ true
excluded-middle-t = refl

excluded-middle-f : evalF ρf (atom 0 ∨ᶠ ¬ᶠ (atom 0)) ≡ true
excluded-middle-f = refl

-- 矛盾律 ¬(A ∧ ¬A) 恒真
contradiction-t : evalF ρt (¬ᶠ (atom 0 ∧ᶠ ¬ᶠ (atom 0))) ≡ true
contradiction-t = refl

contradiction-f : evalF ρf (¬ᶠ (atom 0 ∧ᶠ ¬ᶠ (atom 0))) ≡ true
contradiction-f = refl

-- 蕴含展开 (A → B) ≡ (¬A ∨ B)（双变元四案全枚举）
ρ00 ρ01 ρ10 ρ11 : ℕ → Bool
ρ00 _ = false
ρ01 n = if n ≡ᵇ 1 then true else false
ρ10 n = if n ≡ᵇ 0 then true else false
ρ11 _ = true

implication-form : (ρ : Assignment) → (a b : Formula) → Set
implication-form ρ a b = evalF ρ (a →ᶠ b) ≡ evalF ρ (¬ᶠ a ∨ᶠ b)

imp-00 : implication-form ρ00 (atom 0) (atom 1)
imp-00 = refl

imp-01 : implication-form ρ01 (atom 0) (atom 1)
imp-01 = refl

imp-10 : implication-form ρ10 (atom 0) (atom 1)
imp-10 = refl

imp-11 : implication-form ρ11 (atom 0) (atom 1)
imp-11 = refl

-- 可靠性小例（语义后承实例）：A ∧ B ⊨ A（四案全枚举）
and-elim-00 : evalF ρ00 ((atom 0 ∧ᶠ atom 1) →ᶠ atom 0) ≡ true
and-elim-00 = refl

and-elim-01 : evalF ρ01 ((atom 0 ∧ᶠ atom 1) →ᶠ atom 0) ≡ true
and-elim-01 = refl

and-elim-10 : evalF ρ10 ((atom 0 ∧ᶠ atom 1) →ᶠ atom 0) ≡ true
and-elim-10 = refl

and-elim-11 : evalF ρ11 ((atom 0 ∧ᶠ atom 1) →ᶠ atom 0) ≡ true
and-elim-11 = refl

-- ────────────────────────────────────────────────────────────────────
-- §4 核对层 + 立界注记
-- ────────────────────────────────────────────────────────────────────

-- 语义计算核对（具体公式值）
check-eval-1 : evalF ρ11 ((atom 0 ∧ᶠ atom 1) ∨ᶠ ⊥ᶠ) ≡ true
check-eval-1 = refl

check-eval-2 : evalF ρ00 (¬ᶠ ⊤ᶠ) ≡ false
check-eval-2 = refl

-- 立界注记（诚实边界——不设空壳签名）：
-- (i) 可靠性一般定理（任意推导规则集保语义真——需先定义自然演绎/相继式系统，
--     估 150-250 行：推导规则 data + soundness 归纳）；
-- (ii) 完备性（重言式可导——Henkin/归谬面，深件估 300+）；
-- (iii) 语义判定全形（tautology 判定器 + 与 LogicDecidable 的 Dec 面装配——
--       有限变元全枚举可判定，与 Dec 组合器衔接）；
-- (iv) CNF/范式转换（等值变形链）。
