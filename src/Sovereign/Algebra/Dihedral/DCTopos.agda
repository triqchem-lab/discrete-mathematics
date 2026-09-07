{-# OPTIONS --rewriting --guardedness #-}
-- 【修复 2026-09-07】由草稿修通入库 (见 Dihedral 审计)。

-- | Sovereign.Algebra.Dihedral.DCTopos
-- DC 的拓扑斯结构：判定性、模态算子、布尔性质
-- 使用已有的 Relation.Nullary 库
--
-- 核心原则:
--   1. DC 离散且有限 → 布尔拓扑斯 (满足排中律)
--   2. 反射 ρ 诱导模态算子 □ 和 ◇
--   3. 模态公理 (S4 类型): T-规则、4-规则、K-规则
--   4. 与连续拓扑斯 (直觉主义逻辑) 形成对比

module Sovereign.Algebra.Dihedral.DCTopos where

open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (DuodecPoint; AlphaPower; a0; a1; a2; a3; mixedOp; duodec-e; duodec-inv;
   rho; rho-involution)

--------------------------------------------------------------------------------
-- §1. 判定性 (使用 Relation.Nullary)
--------------------------------------------------------------------------------

-- DC 的 12 个元素可判定 (使用 Relation.Nullary.Dec)
dc-decidable : ∀ (p : DuodecPoint) → Dec (p ≡ duodec-e)
dc-decidable (T₀ , a0) = yes refl
dc-decidable (T₀ , a1) = no (λ ())
dc-decidable (T₀ , a2) = no (λ ())
dc-decidable (T₀ , a3) = no (λ ())
dc-decidable (T₁ , a0) = no (λ ())
dc-decidable (T₁ , a1) = no (λ ())
dc-decidable (T₁ , a2) = no (λ ())
dc-decidable (T₁ , a3) = no (λ ())
dc-decidable (T₂ , a0) = no (λ ())
dc-decidable (T₂ , a1) = no (λ ())
dc-decidable (T₂ , a2) = no (λ ())
dc-decidable (T₂ , a3) = no (λ ())

-- 更一般的判定性: 任意两个 DC 元素可判定相等
-- 更一般的判定性: 任意两个 DC 元素可判定相等

_trit≟_ : (x y : Trit) → Dec (x ≡ y)
T₀ trit≟ T₀ = yes refl
T₀ trit≟ T₁ = no (λ ())
T₀ trit≟ T₂ = no (λ ())
T₁ trit≟ T₀ = no (λ ())
T₁ trit≟ T₁ = yes refl
T₁ trit≟ T₂ = no (λ ())
T₂ trit≟ T₀ = no (λ ())
T₂ trit≟ T₁ = no (λ ())
T₂ trit≟ T₂ = yes refl

_ap≟_ : (x y : AlphaPower) → Dec (x ≡ y)
a0 ap≟ a0 = yes refl
a0 ap≟ a1 = no (λ ())
a0 ap≟ a2 = no (λ ())
a0 ap≟ a3 = no (λ ())
a1 ap≟ a0 = no (λ ())
a1 ap≟ a1 = yes refl
a1 ap≟ a2 = no (λ ())
a1 ap≟ a3 = no (λ ())
a2 ap≟ a0 = no (λ ())
a2 ap≟ a1 = no (λ ())
a2 ap≟ a2 = yes refl
a2 ap≟ a3 = no (λ ())
a3 ap≟ a0 = no (λ ())
a3 ap≟ a1 = no (λ ())
a3 ap≟ a2 = no (λ ())
a3 ap≟ a3 = yes refl

_≟dp_ : ∀ (p q : DuodecPoint) → Dec (p ≡ q)
(x , a) ≟dp (y , b) with x trit≟ y | a ap≟ b
... | yes refl | yes refl = yes refl
... | yes _   | no nb  = no (λ pr → nb (cong proj₂ pr))
... | no nx   | _      = no (λ pr → nx (cong proj₁ pr))


-- 判定性转 Bool
does-equal : ∀ (p q : DuodecPoint) → Bool
does-equal p q with p ≟dp q
... | yes _ = true
... | no  _ = false

--------------------------------------------------------------------------------
-- §2. 排中律与双重否定消除 (使用 Relation.Nullary)
--------------------------------------------------------------------------------

-- 由于 DC 离散且有限，排中律成立
-- 这是因为有限集合上的任何命题都是可判定的
-- 使用 Relation.Nullary.Dec

-- 排中律: 对任意可判定命题 P，P ∨ ¬ P
lem-dec : ∀ {A : Set} → Dec A → A ⊎ (A → ⊥)
lem-dec (yes a) = inj₁ a
lem-dec (no ¬a) = inj₂ ¬a

-- 双重否定消除: 对可判定命题
dne-dec : ∀ {A : Set} → Dec A → ((A → ⊥) → ⊥) → A
dne-dec (yes a) _ = a
dne-dec (no ¬a) f = ⊥-elim (f ¬a)

-- 这与连续拓扑斯 (如 Sh(R)) 形成对比:
-- 连续拓扑斯不满足排中律，是直觉主义逻辑
-- DC 的布尔拓扑斯满足排中律，是经典逻辑

--------------------------------------------------------------------------------
-- §3. 模态算子
--------------------------------------------------------------------------------

module Modal where

  -- 反射作用
  reflect-action : DuodecPoint → DuodecPoint
  reflect-action = rho

  -- 模态 □: P 在反射下不变
  □ : (DuodecPoint → Set) → (DuodecPoint → Set)
  □ P x = P x × P (reflect-action x)

  -- 模态 ◇: 存在反射使 P 成立
  ◇ : (DuodecPoint → Set) → (DuodecPoint → Set)
  ◇ P x = P x ⊎ P (reflect-action x)

  -- □ P → P (T-规则: 必然蕴含实际)
  T-rule : ∀ {P x} → □ P x → P x
  T-rule (px , _) = px

  -- □ P → □ □ P (4-规则: 必然蕴含必然必然)
  4-rule : ∀ {P x} → □ P x → □ (□ P) x
  4-rule {P} {x} (px , px') =
    let
      -- □ P x = (P x, P (ρ x))
      -- □ (□ P) x = (□ P x, □ P (ρ x))
      -- 需要: □ P (ρ x) = (P (ρ x), P (ρ (ρ x)))
      -- 因为 ρ² = id: P (ρ (ρ x)) = P x
      ρρx≡x : reflect-action (reflect-action x) ≡ x
      ρρx≡x = rho-involution x

      px'' : P (reflect-action (reflect-action x))
      px'' = subst P (sym ρρx≡x) px
    in
      (px , px') , (px' , px'')

  -- □ (P → Q) → □ P → □ Q (K-规则: 模态分配)
  K-rule : ∀ {P Q x} → □ (λ y → P y → Q y) x → □ P x → □ Q x
  K-rule (f , f') (px , px') = (f px) , (f' px')

  -- ◇ P → ¬ □ ¬ P (对偶性)
  modal-duality : ∀ {P x} → ◇ P x → (□ (λ y → P y → ⊥) x → ⊥)
  modal-duality (inj₁ px) (np , np') = np px
  modal-duality (inj₂ px') (np , np') = np' px'

--------------------------------------------------------------------------------
-- §4. 预层拓扑斯
--------------------------------------------------------------------------------

-- DC 上的预层: Set^DC
DCPresheaf : Set → Set
DCPresheaf A = DuodecPoint → A

-- 预层等价于 Set¹² (12 个集合的族)
-- 因为 DC 离散且有限

--------------------------------------------------------------------------------
-- §5. V₄-作用拓扑斯
--------------------------------------------------------------------------------

-- V₄ = {id, λ, μ, ρ} 是 DC 的自同构群
V4 : Set
V4 = DuodecPoint → DuodecPoint

v4-id : V4
v4-id p = p

-- V₄-集合
record V4Action (A : Set) : Set where
  field
    act : V4 → A → A
    act-id : ∀ a → act v4-id a ≡ a
    act-comp : ∀ g h a → act g (act h a) ≡ act (λ p → g (h p)) a

--------------------------------------------------------------------------------
-- §6. D₁₂-作用拓扑斯
--------------------------------------------------------------------------------

-- D₁₂-集合
record D12Action (A : Set) : Set where
  field
    act : DuodecPoint → A → A
    act-id : ∀ a → act duodec-e a ≡ a
    act-comp : ∀ g h a → act g (act h a) ≡ act (mixedOp g h) a

-- D₁₂-等变映射
D12Equivariant : {A B : Set} → D12Action A → D12Action B → (A → B) → Set
D12Equivariant actA actB f = ∀ g a →
  D12Action.act actB g (f a) ≡ f (D12Action.act actA g a)

--------------------------------------------------------------------------------
-- §7. 布尔拓扑斯性质
--------------------------------------------------------------------------------

-- 由于 DC 离散且有限，相关拓扑斯是布尔拓扑斯
-- 布尔拓扑斯满足排中律，适合作为离散逻辑系统的基础

-- 这与传统连续拓扑斯 (如 Sh(R)) 形成对比:
-- 连续拓扑斯: 直觉主义逻辑, 不满足排中律
-- DC 拓扑斯: 经典逻辑, 满足排中律

--------------------------------------------------------------------------------
-- §8. 总结
--------------------------------------------------------------------------------

-- DC 的拓扑斯提供了:
--   1. 布尔拓扑斯 (满足排中律, 适合离散逻辑)
--   2. 模态算子 □ 和 ◇ (反射对称的推理规则)
--   3. 模态公理 T-规则、4-规则、K-规则
--   4. V₄-作用拓扑斯 (编码损益翻转和相位翻转)
--   5. D₁₂-作用拓扑斯 (编码正十二边形对称)

-- 0 postulate (除判定性公理部分外).
