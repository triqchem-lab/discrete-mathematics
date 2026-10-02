{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.Finiteness.Foundations
-- 任务书第一层·§1 载体与传输机件（定义层）— 有限性动物园的地基
--
-- 数学背景：
--   Dedekind (1888)：S 有限 ⟺ 每个单射 S→S 都是满射（第一个不依赖自然数的有限概念）。
--   本层立场：**型有限为原语** —— Finite A = Σ ℕ (A ≃ Fin n)；经典 zoo 定义
--   （Dedekind/Tarski）在本层是被证的定理或被声明的缺口，不是公理。
--
-- 【连续统缺陷对照（docs/群论红灯审查-离散全息修复.md；memory/lean-libraries-gap-analysis.md）】
--   经典有限性理论长在连续统基座上：Dedekind 量化任意集合自映射、Tarski 量化幂集，
--   都预设经典无穷/幂集装置；本库**构造主义、无 Choice、无连续统、无 funext**，
--   故一切需要排中律/Choice 的方向不入本库，只作缺口声明（见 FinitenessZoo §5）。
--   与六缺陷框架同一纪律：「焊死的精确范围以表为准——未焊死的如实标注，不以断言代替证明」。
--
-- 【依赖类型论展示群对齐（docs/duodecimal/11 号）】本模块是**定义/定理层**，非展示群
--   本体，八要素（载体/生成元/关系/相位/时钟/归零/刚性/核对）不构成其公理候选
--   （M8 判据 4：定义层不升公理；核对 = refl 穷举，refl 仅确认定义自洽、不产生结构，
--   11 号 :93）。根基接口：载体根 = Base/Trit（GF(3) 及其扩展），Trit ≅ Fin 3 由
--   Geometry/TorusGeometry.tritOf/finOf 给出；本层 Fin n 是 GF(3) 扩展的载体形状
--   （Fin 3^k；T⁶ = 3⁶ = 729 见 Structology/T6 t6Cardinality）。
--
-- 复用：PlatonicTorusProjection._≃_（to/from/to-from/from-to）。
-- 0 postulate / 0 hole。
module Sovereign.Analysis.Finiteness.Foundations where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong)
open import Sovereign.Structology.PlatonicTorusProjection using (_≃_)

--------------------------------------------------------------------------------
-- §1. 有限性定义
--------------------------------------------------------------------------------

InjA : ∀ {A : Set} → (A → A) → Set
InjA {A} f = ∀ a b → f a ≡ f b → a ≡ b

SurjA : ∀ {A : Set} → (A → A) → Set
SurjA {A} f = ∀ i → Σ A (λ j → f j ≡ i)

-- Dedekind 有限性（1888）：每个单射 S→S 都是满射
DedekindFinite : (A : Set) → Set
DedekindFinite A = (f : A → A) → InjA f → SurjA f

-- 型有限性（类型论标准定义）：存在 A ≃ Fin n
-- （Σ-类型载体，11 号 :13；Fin n 由 fzero/fsuc 构造生成 —— 结构 = 生成方式）
Finite : (A : Set) → Set
Finite A = Σ ℕ (λ n → A ≃ Fin n)

--------------------------------------------------------------------------------
-- §1b. ≃ 传输机件（任务书 A2/A3）：to/from 是单射（往返式标准证）
--------------------------------------------------------------------------------

≃-to-inj : ∀ {A B : Set} (e : A ≃ B) (a b : A) → _≃_.to e a ≡ _≃_.to e b → a ≡ b
≃-to-inj e a b eq = trans (sym (_≃_.from-to e a)) (trans (cong (_≃_.from e) eq) (_≃_.from-to e b))

≃-from-inj : ∀ {A B : Set} (e : A ≃ B) (a b : B) → _≃_.from e a ≡ _≃_.from e b → a ≡ b
≃-from-inj e a b eq = trans (sym (_≃_.to-from e a)) (trans (cong (_≃_.to e) eq) (_≃_.to-from e b))
