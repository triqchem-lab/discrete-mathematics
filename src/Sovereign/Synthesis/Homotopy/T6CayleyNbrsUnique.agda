{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyNbrsUnique
--
-- **邻居表不重复**：`Unique (neighbours x)` 的完整组装
--
-- ## 依赖（全部已证且有回执）
--
-- 相邻对共 **4 类**，各有一条已证的引理（`T6CayleyVecOther`）：
--   ① 同坐标 1 vs 2：`updAt-neq-two`
--   ② 跨坐标 1 vs 1：`updAt-neq-other`
--   ③ 跨坐标 2 vs 1：`updAt-neq-other2'`
--   ④ 跨坐标 2 vs 2：`updAt-neq-two-two`
-- 以及 `T6CayleyNbrsNodup` 的 ③ `nbrsFrom-not-in` 与 `∉-to-≢`。
--
-- ## 结构要点（本链唯一的结构发现）
--
-- `Unique = AllPairs _≉_`（stdlib 2.4 把 `Nodup` 改名成了它），构造子
--   `AP._∷_ : All (R x) xs → AllPairs xs → AllPairs (x ∷ xs)`
-- ⇒ 第二个参数必须是**尾表自身**的 `AllPairs` ⇒ 表头有两个元素 ⇒ 必须**双层** `AP._∷_`。
--
-- ## 核心原则
--   · 0 postulate / 0 hole

module Sovereign.Synthesis.Homotopy.T6CayleyNbrsUnique where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Fin.Properties using (suc-injective)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AP
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec; updAt)
open import Sovereign.Synthesis.Homotopy.T6CayleyVecOther
  using (updAt-neq-two; updAt-neq-other; updAt-neq-other2
        ; updAt-neq-other2'; updAt-neq-two-two)
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (nbrsFrom; allFinD; neighbours)
open import Sovereign.Synthesis.Homotopy.T6CayleyNbrsNodup
  using (nbrsFrom-not-in; ∉→All)

--------------------------------------------------------------------------------
-- §1. `∉` 与 `All (_≢_)` 的互相转换（stdlib 没有直接给）
--------------------------------------------------------------------------------

All→∉ : ∀ {n : ℕ} (k : Fin n) (ks : List (Fin n)) → All.All (k ≢_) ks → k ∉ ks
All→∉ k ks all = λ p → All.lookup all p refl

-- 泛化版（`T6CayleyNbrsNodup` 里的那条写死了 `allFinD n`）
∉-to-≢-gen : ∀ {n : ℕ} (j i : Fin n) (xs : List (Fin n))
       → j ∉ xs → i ∈ xs → j ≢ i
∉-to-≢-gen j i xs j∉ i∈ j≡i = j∉ (subst (λ z → z ∈ xs) (sym j≡i) i∈)

--------------------------------------------------------------------------------
-- §2. ★★ 主定理：`js` 不重复 ⇒ 邻居表不重复
--------------------------------------------------------------------------------

k-out : ∀ {n : ℕ} (x : T6Vec n) (k : Fin n) (ks : List (Fin n))
      → k ∉ ks → updAt k x ∉ nbrsFrom x ks
k-out x k ks k∉ = nbrsFrom-not-in x ks (updAt k x)
  (λ i i∈ → updAt-neq-other  k i x (∉-to-≢-gen k i ks k∉ i∈))
  (λ i i∈ → updAt-neq-other2 k i x (∉-to-≢-gen k i ks k∉ i∈))

nbrsFrom-Unique : ∀ {n : ℕ} (x : T6Vec n) (js : List (Fin n))
                → Unique {A = Fin n} js → Unique {A = T6Vec n} (nbrsFrom x js)
nbrsFrom-Unique x []       uniq = AP.[]
nbrsFrom-Unique x (k ∷ ks) (AP._∷_ kAll ksUniq) =
  AP._∷_ h1All (AP._∷_ h2All (nbrsFrom-Unique x ks ksUniq))
  where
  k∉ : k ∉ ks
  k∉ = All→∉ k ks kAll

  h1All : All.All (updAt k x ≢_) (updAt k (updAt k x) ∷ nbrsFrom x ks)
  h1All = All._∷_ (updAt-neq-two k x)
                  (∉→All (updAt k x) (nbrsFrom x ks) (k-out x k ks k∉))

  h2All : All.All (updAt k (updAt k x) ≢_) (nbrsFrom x ks)
  h2All = ∉→All (updAt k (updAt k x)) (nbrsFrom x ks)
            (nbrsFrom-not-in x ks (updAt k (updAt k x))
              (λ i i∈ → updAt-neq-other2' k i x (∉-to-≢-gen k i ks k∉ i∈))
              (λ i i∈ → updAt-neq-two-two  k i x (∉-to-≢-gen k i ks k∉ i∈)))
--------------------------------------------------------------------------------
-- §3. ★ `allFinD` 自身不重复（邻居表刻画的最后一步）
--
-- `allFinD (suc n) = Fin.zero ∷ map Fin.suc (allFinD n)`，所以需要两件：
--   ① 每个 `map Fin.suc` 出来的元素都**不是** `Fin.zero`（构造子冲突，`λ ()`）
--   ② `Fin.suc` 保持不重复（`suc-injective`，stdlib 已有）
--------------------------------------------------------------------------------

suc-neq : ∀ {n : ℕ} {i j : Fin n} → i ≢ j → Fin.suc i ≢ Fin.suc j
suc-neq i≢j h = i≢j (suc-injective h)

zero≢suc : ∀ {n : ℕ} (xs : List (Fin n)) → All.All (Fin.zero ≢_) (map Fin.suc xs)
zero≢suc []       = All.[]
zero≢suc (x ∷ xs) = All._∷_ (λ ()) (zero≢suc xs)

Unique-map-suc : ∀ {n : ℕ} {xs : List (Fin n)}
               → Unique {A = Fin n} xs → Unique {A = Fin (suc n)} (map Fin.suc xs)
Unique-map-suc {xs = []}     AP.[]                = AP.[]
Unique-map-suc {xs = x ∷ xs} (AP._∷_ all rest)    =
  AP._∷_ (map⁺ (All.map (λ i≢j → suc-neq i≢j) all)) (Unique-map-suc rest)

allFinD-Unique : ∀ (n : ℕ) → Unique {A = Fin n} (allFinD n)
allFinD-Unique zero    = AP.[]
allFinD-Unique (suc n) =
  AP._∷_ (zero≢suc (allFinD n)) (Unique-map-suc (allFinD-Unique n))
--------------------------------------------------------------------------------
-- §4. ★★★ 最终形式：**邻居表不重复**
--------------------------------------------------------------------------------

neighbours-Unique : ∀ {n : ℕ} (x : T6Vec n) → Unique {A = T6Vec n} (neighbours x)
neighbours-Unique {n} x = nbrsFrom-Unique x (allFinD n) (allFinD-Unique n)

