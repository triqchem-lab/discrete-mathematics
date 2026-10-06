{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.InjSurj
-- P0-1: Dedekind 有限性——injSurj 推广到有限类型
--
-- 任务书 1.1：Dedekind (1888) 有限性定义
--   S Dedekind 有限 ⟺ 每个单射 S→S 是满射
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.InjSurj where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero)

open import Sovereign.Base.Trit using (Trit)

--------------------------------------------------------------------------------
-- §1. 泛型定义
--------------------------------------------------------------------------------

Injective : ∀ {A B : Set} → (A → B) → Set
Injective {A} f = ∀ {x y : A} → f x ≡ f y → x ≡ y

Surjective : ∀ {A B : Set} → (A → B) → Set
Surjective {A} {B} f = ∀ (b : B) → Σ A (λ a → f a ≡ b)

DedekindFinite : Set → Set
DedekindFinite A = ∀ (f : A → A) → Injective f → Surjective f

record Finite (A : Set) : Set₁ where
  field
    n : ℕ
    to   : A → Fin n
    from : Fin n → A
    to-from : ∀ (i : Fin n) → to (from i) ≡ i
    from-to : ∀ (a : A) → from (to a) ≡ a

open Finite

--------------------------------------------------------------------------------
-- §2. Fin 3 版完整闭合（jac_Pigeonhole 导出）
--------------------------------------------------------------------------------

open import Sovereign.Algebra.Jacobian.jac_Pigeonhole
  using (pigeonhole-1)

trit-dedekind : DedekindFinite Trit
trit-dedekind f inj b = pigeonhole-1 f inj b

--------------------------------------------------------------------------------
-- §3. Injective 传输：Injective f → Injective (to ∘ f ∘ from)
--------------------------------------------------------------------------------

-- Injective (to fin) 由 from-to 保证
injective-to : ∀ {A : Set} {n : ℕ} (fin : Finite A) → Injective (to fin)
injective-to {A} {n} fin {a} {b} eq =
  trans (sym (from-to fin a)) (trans (cong (from fin) eq) (from-to fin b))
-- 这正是 step 1 的证明！

-- Injective f → Injective (to ∘ f ∘ from)
-- eq : to(f(from x)) ≡ to(f(from y))
-- ⟹ f(from x) ≡ f(from y)  [injective-to]
-- ⟹ from x ≡ from y         [injective f]
-- ⟹ to(from x) ≡ to(from y) [cong to]
-- ⟹ x ≡ y                    [to-from]
inj-compose-real : ∀ {A : Set} {n : ℕ} (fin : Finite A) → (f : A → A) →
                   Injective f → Injective (to fin ∘ f ∘ from fin)
inj-compose-real {A} {n} fin f inj {x} {y} eq =
  let step1 = injective-to {A} {n} fin {f (from fin x)} {f (from fin y)} eq
      step2 = inj {from fin x} {from fin y} step1
  in trans (sym (to-from fin x))
           (trans (cong (to fin) step2) (to-from fin y))

--------------------------------------------------------------------------------
-- §4. Surjective 传输：Surjective (to ∘ f ∘ from) → Surjective f
--
--   Given b : A, we need to find a : A with f a ≡ b.
--   Let b' = to b : Fin n. By Surjective (to∘f∘from), ∃ a', to(f(from a')) ≡ b'.
--   Let a = from a'. Then:
--     f a = f (from a')
--         ≡ from (to (f (from a')))   [from-to (f (from a'))]
--         ≡ from b'                    [cong from (eq)]
--         = from (to b)                [by definition of b']
--         ≡ b                          [from-to b]
--------------------------------------------------------------------------------

surj-compose : ∀ {A : Set} {n : ℕ} (fin : Finite A) → (f : A → A) →
               Surjective (to fin ∘ f ∘ from fin) → Surjective f
surj-compose {A} {n} fin f surj b =
  let b'  = to fin b
      (a' , eq) = surj b'
      a   = from fin a'
      -- eq : to fin (f (from fin a')) ≡ to fin b
      -- from (to fin (f a)) ≡ f a   [from-to]
      -- from (to fin b) ≡ b         [from-to]
      fa≡from-b' = trans (sym (from-to fin (f (from fin a'))))
                         (trans (cong (from fin) eq)
                                (from-to fin b))
      -- fa≡from-b' : f (from fin a') ≡ from fin (to fin b) ≡ b
  in (a , fa≡from-b')

--------------------------------------------------------------------------------
-- §5. Finite→DedekindFinite 完整定理
--
--   需要 Pigeonhole 肯定版：Fin n 上单射 ⟹ 满射
--   当前可用：Trit (Fin 3) 版 pigeonhole-1
--   Fin n 泛型版需要 pigeonhole 肯定版——P1-1 双向等价补全
--
--   Trit 版完整实例：
--     Finite Trit (n=3, to=fin3ToTrit, from=tritToFin3)
--     Finite→DedekindFinite fin f inj = surj-compose ... (pigeonhole-trit ...)
--
--   Fin n 泛型版：injective-to + inj-compose-real + surj-compose + pigeonhole-neg
--     全部可用——只是 Fin n 的 pigeonhole 肯定版缺一个封闭引理
--     现有 stdlib pigeonhole 提供否定版（m > n → ¬ Injective f），
--     肯定版（Injective f → Surjective f）在 jac_Pigeonhole 中只对 Trit 闭合。
--
--   结论：Trit 版完整闭合；Fin n 泛型版留 roadmap（P1-1 双向等价）。
--   证明核心架构已完整（injective-to + surj-compose + pigeonhole-neg）

-- Fin 0 版（vacuously true）
dedekind-fin0 : DedekindFinite (Fin 0)
dedekind-fin0 f inj ()
