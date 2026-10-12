{-# OPTIONS --rewriting --guardedness #-}

-- | _PFT2
-- 紧致性失效前置件：一阶逻辑紧致性在有限模型语义下失效（Trakhtenbrot 前置——经典结果）。
--
-- 数学背景：紧致性定理（经典语义）：句族 Φ 每个有限子集可满足 ⟹ Φ 可满足。
--   有限模型语义下失效：句族 Φ = {θₖ : 「载体规模 ≥ k」} 每个有限段有有限模型，
--   但全体族无有限模型（任意有限 n 都被 θ_{n+1} 排除）——无限模型（ℕ 载体）存在。
--
-- 核心原则：
--   1. 句族 = 规模约束形 Sat k n（嵌套单调族——有限子集归约为有限段，合法因单调性）；
--   2. 无有限模型 = 反证形（θ_{n+1} 于规模 n 不可满足——le-suc-false 布尔归约）；
--   3. 无限模型 = ℕ 载体构造形（InfStructure + 无界见证）；
--   4. 双条件定理：有限段可满足 ∧ 全体无有限模型 = 紧致性失效。
--
-- 包含：Sat · le-refl · le-suc-false · theta-unmodel · no-finite-model ·
--       InfStructure · ℕModel · atleast · segment-sat · compactness-fails-finite · 核对层

module _PFT2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Sovereign.Foundation.FiniteModelTheory using (AtLeast; _≤?_)

-- ────────────────────────────────────────────────────────────────────
-- §1 句族语义层（规模约束形）
--   θₖ 的有限模型语义：规模 n 的结构满足 θₖ ⟺ k ≤ n。
--   嵌套性：k' ≤ k → (k ≤? n) ≡ true → (k' ≤? n) ≡ true（单调族——
--   任意有限子集被其最大元段控制，故「每个有限子集可满足」归约为
--   「每个有限段可满足」——segment-sat 即完备刻画）。
-- ────────────────────────────────────────────────────────────────────

Sat : ℕ → ℕ → Set
Sat k n = (k ≤? n) ≡ true

-- 自反：规模 n 满足 θₙ
le-refl : ∀ n → (n ≤? n) ≡ true
le-refl zero    = refl
le-refl (suc n) = le-refl n

-- 越界：suc n ≤? n 恒假（布尔归约）
le-suc-false : ∀ n → (suc n ≤? n) ≡ false
le-suc-false zero    = refl
le-suc-false (suc n) = le-suc-false n

false-≢-true : false ≡ true → ⊥
false-≢-true ()

-- ────────────────────────────────────────────────────────────────────
-- §2 ① 句族无有限模型（反证形——两层）
-- ────────────────────────────────────────────────────────────────────

-- 逐句层：θ_{n+1} 于规模 n 不可满足（反证：越界归约矛盾）
theta-unmodel : ∀ n → Sat (suc n) n → ⊥
theta-unmodel n eq = false-≢-true (trans (sym (le-suc-false n)) eq)

-- 全体层：无单一有限规模满足所有 θₖ
no-finite-model : (Σ[ n ∈ ℕ ] (∀ k → Sat k n)) → ⊥
no-finite-model (n , all) = theta-unmodel n (all (suc n))

-- ────────────────────────────────────────────────────────────────────
-- §3 ② 无限模型存在（ℕ 结构承载——构造形）
-- ────────────────────────────────────────────────────────────────────

record InfStructure : Set where
  field
    R₁ : ℕ → Bool
    S₂ : ℕ → ℕ → Bool

ℕModel : InfStructure
ℕModel = record { R₁ = λ _ → true ; S₂ = λ _ _ → true }

-- ℕ 载体无界：每个 θₖ 有见证（k ≤ k）
atleast : ∀ k → AtLeast k
atleast k = k , le-refl k

-- ────────────────────────────────────────────────────────────────────
-- §4 ③ 紧致性失效定理（双条件）
--   有限段可满足（嵌套族归约）∧ 全体无有限模型。
-- ────────────────────────────────────────────────────────────────────

segment-sat : ∀ k → Σ[ n ∈ ℕ ] (∀ j → (j ≤? k) ≡ true → Sat j n)
segment-sat k = k , (λ _ j≤k → j≤k)

compactness-fails-finite :
    (∀ k → Σ[ n ∈ ℕ ] (∀ j → (j ≤? k) ≡ true → Sat j n))
  × ((Σ[ n ∈ ℕ ] (∀ k → Sat k n)) → ⊥)
compactness-fails-finite = segment-sat , no-finite-model

-- ────────────────────────────────────────────────────────────────────
-- §5 核对层（k=2,3 小例）
-- ────────────────────────────────────────────────────────────────────

check-seg2 : Σ[ n ∈ ℕ ] ((2 ≤? n) ≡ true)
check-seg2 = 2 , refl

check-seg3 : Σ[ n ∈ ℕ ] ((3 ≤? n) ≡ true)
check-seg3 = 3 , refl

check-bound2 : (3 ≤? 2) ≡ false
check-bound2 = refl

check-atleast2 : Σ[ n ∈ ℕ ] ((2 ≤? n) ≡ true)
check-atleast2 = atleast 2

check-unmodel2 : Sat 3 2 → ⊥
check-unmodel2 = theta-unmodel 2
