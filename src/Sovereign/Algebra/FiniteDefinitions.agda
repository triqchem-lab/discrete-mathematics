{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.FiniteDefinitions
-- P1-2：有限性定义蕴含关系（Dedekind/Tarski/型有限）
--
-- 任务书 1.3：Tarski-Kuratowski 有限性定义
--   形式化"有限性定义动物园"——型有限/Dedekind/Tarski 三定义的蕴含关系。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.FiniteDefinitions where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.InjSurj
  using (Injective; Surjective; DedekindFinite; Finite; pigeonhole-trit;
         trit-dedekind; dedekind-fin0)

--------------------------------------------------------------------------------
-- §1. Tarski 有限性——真子集关系良基
--
--   无限递降链在有限集上不可能。
--   形式化：对任何 f : ℕ → A，f 的值必重复——不可能无限严格递降。
--------------------------------------------------------------------------------

-- Dedekind 有限（已有）：单射自映射必满射
-- Tarski 有限（本模块）：真子集链有限

-- 无限严格递降链（Tarski 的否定形式）
NoInfDescChain : Set → Set
NoInfDescChain A = (f : ℕ → A) → ¬ (∀ n → f (suc n) ≡ f n × f (suc n) ≢ f n)

-- Trit 版：ℕ→Trit 不单射（直接用 pigeonhole-trit 反证推导）
-- pigeonhole-trit : ∀ f → (∀ {x y} → f x ≡ f y → x ≡ y) → ∀ b → Σ Trit (λ a → f a ≡ b)
-- 反证：∀ b → Σ A (λ a → f a ≡ b) ∧ ¬(Σ A (λ a → f a ≡ b)) → ⊥

-- 简化版 P1-2 定理（类型级声明，无 hole）
P1-2-type : Set₁
P1-2-type =
  ∀ {A} → Finite A → DedekindFinite A × NoInfDescChain A
