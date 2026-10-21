{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Analysis.DiscreteMeasure
--
-- 离散测度论的最小基石：**计数测度在互不相交集合上可加**。
--
-- ## 数学背景
--
-- 连续统上的测度论需要 σ-代数、可数可加性、Carathéodory 延拓 —— 全部依赖
-- 不可数并 / 极限，本库离散基座不提供（见 `memory/dual_track_constitution.md`）。
-- 有限集上的对应物则是**纯组合**的：令 `Count n = Fin n → Bool`（子集的特征函数），
--   `μ P = #(P)`（满足的格点数），则
--   `Disjoint P Q ⇒ μ (P ∪ᵐ Q) = μ P + μ Q`
-- **不相交前提不可省**：若某点同时属于两者，右侧重复计数而左侧不重复。
--
-- ## 与 `Foundation.CompletenessTheorem` 的关系
--
-- 该模块把 `MeasureTheory` 的离散载体定为 `ℕ`（计数测度），并注明
-- 「缺的是概念特有的结构定律」——**本模块补上的正是那条定律**（可加性）。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；无 `with`（`with` 的抽象会挡住 `refl`，
--     改对**布尔变量**分情形的 `step-lemma`，全程 `refl` + `+-suc`）
--   · 不用 `Data.Complex` / 浮点 / 极限
--------------------------------------------------------------------------------

module Sovereign.Synthesis.Analysis.DiscreteMeasure where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc; ≤-step; +-mono-≤)
open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)

-- `false ≢ true`（本地一行，避开 stdlib 命名差异）
true≢false : true ≢ false
true≢false ()

--------------------------------------------------------------------------------
-- §1. 载体：有限集的特征函数；测度：计数
--------------------------------------------------------------------------------

Count : ℕ → Set
Count n = Fin n → Bool

countᵐ : ∀ {n} → Count n → ℕ
countᵐ {n = zero}  P = 0
countᵐ {n = suc m} P =
  (if P Fin.zero then 1 else 0) + countᵐ {n = m} (λ i → P (Fin.suc i))

--------------------------------------------------------------------------------
-- §2. 集合运算与互不相交
--------------------------------------------------------------------------------

Disjoint : ∀ {n} → Count n → Count n → Set
Disjoint {n} P Q = ∀ (i : Fin n) → P i ≡ true → Q i ≡ true → ⊥

_∪ᵐ_ : ∀ {n} → Count n → Count n → Count n
(P ∪ᵐ Q) i = P i ∨ Q i

-- 尾部保持互不相交
disj-tail : ∀ {m} {P Q : Count (suc m)} → Disjoint P Q
          → Disjoint (λ i → P (Fin.suc i)) (λ i → Q (Fin.suc i))
disj-tail d i p q = d (Fin.suc i) p q

--------------------------------------------------------------------------------
-- §3. ★ 关键一步：对**布尔变量**分情形
--
-- 之所以不直接在 `countᵐ-∪ᵐ` 里 `with P zero`：`with` 会把 `P zero` 抽象成变量，
-- 于是「`P zero` 就是 `true`」只能**命题地**拿到，`refl` 闭合不了。
-- 把两个布尔量提成**参数**，四个情形全是 `refl`（`true/true` 由互不相交排除）。
--------------------------------------------------------------------------------

step-lemma : ∀ (a b : Bool) → (a ≡ true → b ≡ true → ⊥)
           → ∀ X Y Z → X ≡ Y + Z
           → (if a ∨ b then 1 else 0) + X
           ≡ (if a then 1 else 0) + Y + ((if b then 1 else 0) + Z)
step-lemma false false _ X Y Z e = e
step-lemma false true  _ X Y Z e = trans (cong suc e) (sym (+-suc Y Z))
step-lemma true  false _ X Y Z e = trans (cong suc e) refl
step-lemma true  true  d _ _ _ _ = ⊥-elim (d refl refl)

--------------------------------------------------------------------------------
-- §4. ★★ 可加性：不相交前提不可省
--------------------------------------------------------------------------------

countᵐ-∪ᵐ : ∀ {n} (P Q : Count n) → Disjoint P Q
        → countᵐ (P ∪ᵐ Q) ≡ countᵐ P + countᵐ Q
countᵐ-∪ᵐ {n = zero}  P Q _ = refl
countᵐ-∪ᵐ {n = suc m} P Q disj =
  step-lemma (P Fin.zero) (Q Fin.zero) (disj Fin.zero)
             (countᵐ (λ i → P (Fin.suc i) ∨ Q (Fin.suc i)))
             (countᵐ (λ i → P (Fin.suc i)))
             (countᵐ (λ i → Q (Fin.suc i)))
             (countᵐ-∪ᵐ (λ i → P (Fin.suc i)) (λ i → Q (Fin.suc i)) (disj-tail disj))

--------------------------------------------------------------------------------
-- §5. 计算验证（具体点：n = 2，P = {0}、Q = {1}，μ(P∪ᵐQ) = 2 = 1 + 1）
--------------------------------------------------------------------------------

P₂ Q₂ : Count 2
P₂ Fin.zero          = true
P₂ (Fin.suc Fin.zero) = false
Q₂ Fin.zero          = false
Q₂ (Fin.suc Fin.zero) = true

check-μ : countᵐ (P₂ ∪ᵐ Q₂) ≡ 2
check-μ = refl

check-加 : countᵐ (P₂ ∪ᵐ Q₂) ≡ countᵐ P₂ + countᵐ Q₂
check-加 = countᵐ-∪ᵐ P₂ Q₂ disj-PQ
  where
    disj-PQ : Disjoint P₂ Q₂
    disj-PQ Fin.zero          p q = true≢false (sym q)
    disj-PQ (Fin.suc Fin.zero) p q = true≢false (sym p)

--------------------------------------------------------------------------------
-- §6. ★ 单调性：`P ⊆ Q ⇒ countᵐ P ≤ countᵐ Q`（测度的另一条基本公理）
--------------------------------------------------------------------------------

subset : ∀ {n} → Count n → Count n → Set
subset {n} P Q = ∀ (i : Fin n) → P i ≡ true → Q i ≡ true

-- 尾部保持包含（顶层，避免 where 与 with 的作用域限制）
subset-tail : ∀ {m} {P Q : Count (suc m)} → subset P Q
            → subset (λ i → P (Fin.suc i)) (λ i → Q (Fin.suc i))
subset-tail sub i p = sub (Fin.suc i) p

-- 关键一步：对**布尔变量**分情形（不用 with，避免抽象挡住矛盾）
mono-step-count : ∀ (a b : Bool) → (a ≡ true → b ≡ true)
          → ∀ X Y → X ≤ Y
          → (if a then 1 else 0) + X ≤ (if b then 1 else 0) + Y
mono-step-count false false _ X Y p = p
mono-step-count false true  _ X Y p = ≤-step p
mono-step-count true  false h X Y p = ⊥-elim (true≢false (sym (h refl)))
mono-step-count true  true  _ X Y p = s≤s p

countᵐ-mono : ∀ {n} (P Q : Count n) → subset P Q → countᵐ P ≤ countᵐ Q
countᵐ-mono {n = zero}  P Q _ = z≤n
countᵐ-mono {n = suc m} P Q sub =
  mono-step-count (P Fin.zero) (Q Fin.zero) (sub Fin.zero) _ _
            (countᵐ-mono (λ i → P (Fin.suc i)) (λ i → Q (Fin.suc i)) (subset-tail sub))

--------------------------------------------------------------------------------
-- §7. ★ 其余测度公理：空集测度 0、全集测度 n（归一化）
--------------------------------------------------------------------------------

∅ᵐ : ∀ {n} → Count n
∅ᵐ _ = false

⊤ᵐ : ∀ {n} → Count n
⊤ᵐ _ = true

countᵐ-empty : ∀ {n} → countᵐ (∅ᵐ {n}) ≡ 0
countᵐ-empty {n = zero}  = refl
countᵐ-empty {n = suc m} = countᵐ-empty {n = m}

countᵐ-full : ∀ {n} → countᵐ (⊤ᵐ {n}) ≡ n
countᵐ-full {n = zero}  = refl
countᵐ-full {n = suc m} = cong suc (countᵐ-full {n = m})
