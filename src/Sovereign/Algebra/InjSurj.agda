{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.InjSurj
-- P0-1: Dedekind 有限性——injSurj 推广到任意有限类型
--
-- 任务书 1.1：Dedekind (1888) 有限性定义
--   S Dedekind 有限 ⟺ 每个单射 S→S 是满射
--   等价于：S 不能与任何真子集建立双射
--
-- 形式化切入点：
--   DedekindFinite A = ∀ f → Injective f → Surjective f （定义）
--   Finite→DedekindFinite : Finite A → DedekindFinite A（定理——等价传输）
--
-- 已有资产：jac_Pigeonhole.pigeonhole-1（Trit/Fin 3 版）
-- 依赖：无阻塞
-- 工作量：~80 行
-- 0 postulate / 0 hole。
module Sovereign.Algebra.InjSurj where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat using (ℕ; zero)

open import Sovereign.Base.Trit using (Trit)

--------------------------------------------------------------------------------
-- §1. 泛型定义
--------------------------------------------------------------------------------

Injective : ∀ {A B : Set} → (A → B) → Set
Injective {A} f = ∀ {x y : A} → f x ≡ f y → x ≡ y

Surjective : ∀ {A B : Set} → (A → B) → Set
Surjective {A} {B} f = ∀ (b : B) → Σ A (λ a → f a ≡ b)

-- Dedekind 有限性定义（P0-1 核心）
DedekindFinite : Set → Set
DedekindFinite A = ∀ (f : A → A) → Injective f → Surjective f

-- 有限类型 record（∃ n, A ↔ Fin n）
record Finite (A : Set) : Set₁ where
  field
    n : ℕ
    to   : A → Fin n
    from : Fin n → A
    to-from : ∀ (i : Fin n) → to (from i) ≡ i
    from-to : ∀ (a : A) → from (to a) ≡ a

--------------------------------------------------------------------------------
-- §2. Fin n 版 injSurj（已有 jac_Pigeonhole 导出）
--------------------------------------------------------------------------------

open import Sovereign.Algebra.Jacobian.jac_Pigeonhole
  using (Inj1; Surj1; pigeonhole-1)

-- Trit 版：单射 ⟹ 满射（完整闭合）
pigeonhole-trit : (f : Trit → Trit) →
                  (∀ {x y} → f x ≡ f y → x ≡ y) →
                  (∀ b → Σ Trit (λ a → f a ≡ b))
pigeonhole-trit f inj b = pigeonhole-1 f inj b

--------------------------------------------------------------------------------
-- §3. Finite→DedekindFinite：等价传输（P0-1 核心定理）
--
--   证明策略：
--   ① Finite A 提供 to : A → Fin n 和 from : Fin n → A
--   ② 对给定的 f : A → A，构造 f' = to ∘ f ∘ from : Fin n → Fin n
--   ③ Injective f → Injective f'（等价保持单射性）
--   ④ pigeonhole-trit/Fin n 版给出 Surjective f'
--   ⑤ Surjective f' → Surjective f（等价保持满射性）
--
--   简化版：先用 Trit 版（n=3），泛型 Fin n 版需要一般 pigeonhole 肯定版。
--   当前可验证：Trit 版完整闭合 + 定义级声明。
--
--   ⚠ 完整版 Finite→DedekindFinite 需要：
--      (a) Injective 传输：Injective f → Injective (to ∘ f ∘ from) — 纯函数组合
--      (b) Surjective 传输：Surjective (to ∘ f ∘ from) → Surjective f — 需要 from-to
--      (c) pigeonhole 肯定版（Fin n 上 Injective → Surjective）——P1-1 双向等价
--
--   当前落盘：定义级声明 + Trit 版完整闭合。
--   完整证明标记 roadmap（依赖 P1-1 pigeonhole 肯定版）。
--------------------------------------------------------------------------------

-- 定义级声明（类型正确，无 hole）
Finite→DedekindFinite-type : Set₁
Finite→DedekindFinite-type =
  ∀ {A : Set} → Finite A → DedekindFinite A

-- Trit 版完整实例：pigeonhole-trit 已证
trit-dedekind : DedekindFinite Trit
trit-dedekind f inj b = pigeonhole-trit f inj b

-- Fin 0 版（空类型，vacuously true）
dedekind-fin0 : DedekindFinite (Fin 0)
dedekind-fin0 f inj ()

-- P0-1 完成度：
--   ✅ DedekindFinite 定义（P0-1 核心定义）
--   ✅ Finite record（∃ n, A ↔ Fin n）
--   ✅ pigeonhole-trit（Trit 版完整闭合）
--   ✅ trit-dedekind（Trit 版 Dedekind 有限性实例）
--   ✅ dedekind-fin0（空类型 vacuously true）
--   ✅ Finite→DedekindFinite-type（定义级声明）
--   ⚠ Finite→DedekindFinite 证明体（需 P1-1 pigeonhole 肯定版）
--
--   防虚假完成：无 hole（0 postulate / 0 hole）。
--   Trit 版 = 完整构造性证明（jac_Pigeonhole 导出）。
--   泛型版 = 类型级声明 + roadmap（依赖 P1-1）。
