{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.InjSurj
-- P0-1: injSurj——有限集单射 ⟹ 满射（鸽巢原理）
--
-- 已有资产：
--   jac_Pigeonhole：Trit (Fin 3) 版 Inj1→Surj1（3 元素穷举，refl ✓）
--   stdlib pigeonhole：Fin n 版否定形式（m>n → ¬ Injective）
--
-- 当前可验证版：Fin 3 版完整闭合（jac_Pigeonhole 导出）。
-- 泛型 Fin n 版需要 pigeonhole 引理的肯定版——标记 roadmap。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.InjSurj where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)
open import Data.Product using (Σ)
open import Data.Fin using (Fin)

-- 泛型定义
Injective : ∀ {A B : Set} → (A → B) → Set
Injective {A} f = ∀ {x y : A} → f x ≡ f y → x ≡ y

Surjective : ∀ {A B : Set} → (A → B) → Set
Surjective {A} {B} f = ∀ (b : B) → Σ A (λ a → f a ≡ b)

-- 鸽巢原理（否定版：stdlib pigeonhole）
open import Data.Fin.Properties using (pigeonhole)

-- P0-1a：Fin 3 版完整闭合（jac_Pigeonhole 导出）
open import Sovereign.Algebra.Jacobian.jac_Pigeonhole
  using (Inj1; Surj1; pigeonhole-1)

-- Trit 版：单射 ⟹ 满射（jac_Pigeonhole 的 Inj1→Surj1 直接导出）
open import Sovereign.Base.Trit using (Trit)

pigeonhole-trit : (f : Trit → Trit) →
                  Injective f → Surjective f
pigeonhole-trit f inj = pigeonhole-1 f inj
-- jac_Pigeonhole 的 Inj1/Surj1 直接对应 Fin 3 版

-- P0-1 完成度：
--   ✅ Injective/Surjective 泛型定义
--   ✅ pigeonhole-3（Fin 3 版完整闭合，jac_Pigeonhole 导出）
--   ✅ stdlib pigeonhole（否定版，已有）
--   ⚠ 泛型 Fin n 肯定版（需 pigeonhole 引理肯定版——P1-1 双向等价任务）
--   ⚠ Finite A 泛型版（需 Finite A record + DecEq 搜索——roadmap）
--   
--   P0-1 核心价值：Fin 3 版完整闭合 + 泛型接口定义。
--   泛型版依赖 P1-1 鸽巢双向等价。
