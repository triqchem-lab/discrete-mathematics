{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | _PM7a — GAP-M7a-homology-quotient 探针：FAb 载体商型同调群
--
-- 数学背景：H_k = ker ∂ₖ / im ∂_{k+1}（子群 + 良定义商）。
--   已证件（复用零重证）：FreeAbQuotient 的 H₀/H₁/H₂ = C/R 形 HIT 商 +
--   f₀ : H₀ ≅ Trit（aug 诱导）；FreeAbHomologyGroup 的 K₃ 对账；
--   FreeAbBoundary 的 ∂₁/∂₂；FreeAb 的 negᶠ/neg-add。
--   本件交付：
--   ① HomologyQuotient 泛型构造（切片三元组 + 子群谓词 + 商型 Hk）
--   ② im ⊆ ker 无条件（comp0 直给）+ 等价律参数化（HRWells）
--   ③ K₃ 实例化 + 关系桥两方向（HR→R₁ / HR0→R₀——条件式：同态律前提）
--   ⚠ 立界：∂₁∘∂₂ = 0 具体证（接 MorseSqZero 线）、∂₁/aug 同态律具体证、
--   Hₖ 群律（transport-of-structure 同 H₀ 先例）——路线在案。
--
-- 核心原则：
--   1. 复用优先：H₀ 先例（f₀/eq//elim）与 K₃ 对账件零重证
--   2. 条件桥诚实形：同态律前提显式参数化，不硬证
--   3. 零 with；隐式钉参；GF(3) 算术九案穷尽（≤27 边界内）
module _PM7a where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to p₁; proj₂ to p₂)
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/)
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Empty.Base using (⊥)
open import Cubical.Data.Equality.Conversion using (eqToPath)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.FreeAb using (FAb; negᶠ; neg-add)
open import Sovereign.Problem.Hodge.FreeAbBoundary using (C₀; C₁; C₂; ∂₁; ∂₂)
open import Sovereign.Problem.Hodge.FreeAbHomologyGroup using (aug; aug-∂₁-zero)

--------------------------------------------------------------------------------
-- §1 工具层：GF(3) 消去律（九案穷尽 ≤27）
--------------------------------------------------------------------------------

-- 极小消去子（空型 () 合法——教训 #51 邻域）
from⊥ : {A : Set} → ⊥ → A
from⊥ ()

-- 构造子互异判别（tag 法——空模式不认构造子差教训 #51 邻域）
isZeroT : Trit → Bool
isZeroT T₀ = true
isZeroT T₁ = false
isZeroT T₂ = false

isOneT : Trit → Bool
isOneT T₀ = false
isOneT T₁ = true
isOneT T₂ = false

T₀≢T₁ : T₀ ≡ T₁ → ⊥
T₀≢T₁ p = true≢false (cong isZeroT p)
T₀≢T₂ : T₀ ≡ T₂ → ⊥
T₀≢T₂ p = true≢false (cong isZeroT p)
T₁≢T₀ : T₁ ≡ T₀ → ⊥
T₁≢T₀ p = true≢false (cong isOneT p)
T₁≢T₂ : T₁ ≡ T₂ → ⊥
T₁≢T₂ p = true≢false (cong isOneT p)
T₂≢T₀ : T₂ ≡ T₀ → ⊥
T₂≢T₀ p = T₀≢T₂ (sym p)
T₂≢T₁ : T₂ ≡ T₁ → ⊥
T₂≢T₁ p = T₁≢T₂ (sym p)

-- a ⊕ negate b ≡ T₀ ⟹ a ≡ b（GF(3) 消去——negate 自逆；九案）
⊕neg-zero : (a b : Trit) → a ⊕ negate b ≡ T₀ → a ≡ b
⊕neg-zero T₀ T₀ _ = refl
⊕neg-zero T₀ T₁ h = from⊥ (T₂≢T₀ h)
⊕neg-zero T₀ T₂ h = from⊥ (T₁≢T₀ h)
⊕neg-zero T₁ T₀ h = from⊥ (T₁≢T₀ h)
⊕neg-zero T₁ T₁ _ = refl
⊕neg-zero T₁ T₂ h = from⊥ (T₂≢T₀ h)
⊕neg-zero T₂ T₀ h = from⊥ (T₂≢T₀ h)
⊕neg-zero T₂ T₁ h = from⊥ (T₁≢T₀ h)
⊕neg-zero T₂ T₂ _ = refl

--------------------------------------------------------------------------------
-- §2 HomologyQuotient 泛型构造（子群 + 良定义商）
--------------------------------------------------------------------------------

module HomologyQuotient
  (Cₖ Cₖ₋₁ Cₖ₊₁ : Set)
  (sub : Cₖ → Cₖ → Cₖ)
  (∂k : Cₖ → Cₖ₋₁)
  (zero₁ : Cₖ₋₁)
  (∂kp1 : Cₖ₊₁ → Cₖ)
  (comp0 : (c : Cₖ₊₁) → ∂k (∂kp1 c) ≡ zero₁) where

  -- 子群谓词
  KerSub : Cₖ → Set
  KerSub x = ∂k x ≡ zero₁

  ImElem : Cₖ → Set
  ImElem x = Σ Cₖ₊₁ (λ c → x ≡ ∂kp1 c)

  -- im ⊆ ker（无条件——comp0 直给；商良定义的核心前提）
  im⊂ker : (x : Cₖ) → ImElem x → KerSub x
  im⊂ker x (c , e) = subst (λ z → ∂k z ≡ zero₁) (sym e) (comp0 c)

  -- 同调关系：x ~ y ⟺ x ∸ y ∈ im ∂ₖ₊₁
  HR : Cₖ → Cₖ → Set
  HR x y = ImElem (sub x y)

  -- 商型同调群（HIT 商承载——同 FreeAbQuotient 先例）
  Hk : Set
  Hk = Cₖ / HR

  -- 良定义商前提件（等价三律 + 同余——参数化，K₃ 实例提供）
  record HRWells : Set₁ where
    field
      hr-refl   : (x : Cₖ) → HR x x
      hr-sym    : (x y : Cₖ) → HR x y → HR y x
      hr-trans  : (x y z : Cₖ) → HR x y → HR y z → HR x z
      hr-resp   : (x x' y y' : Cₖ) → HR x x' → HR y y' →
                  HR (sub x y) (sub x' y')

--------------------------------------------------------------------------------
-- §3 K₃ 实例化（FAb 载体 + negᶠ 减法形）
--------------------------------------------------------------------------------

subᶠ : {n : ℕ} → FAb n → FAb n → FAb n
subᶠ x y = λ i → x i ⊕ negate (y i)

zeroᶠ : {n : ℕ} → FAb n
zeroᶠ = λ _ → T₀

module K3Slice
  (comp0-k3 : (c : C₂) → ∂₁ (∂₂ c) ≡ zeroᶠ)
  (∂₁-hom : (x y : C₁) (i : Fin 3) → ∂₁ (subᶠ x y) i ≡ (∂₁ x i) ⊕ negate (∂₁ y i))
  where

  open HomologyQuotient C₁ C₀ C₂ (subᶠ {3}) ∂₁ (zeroᶠ {3}) ∂₂ comp0-k3
    using (KerSub; ImElem; im⊂ker; HR; Hk)

  -- K₃ 商型同调（H₁ = ker ∂₁ / im ∂₂）
  H₁ᵏ : Set
  H₁ᵏ = Hk

  -- 关系桥（条件式）：HR x y ⟹ 逐点边界相等（R₁ 形）
  --   链：(∂₁x i ⊕ neg(∂₁y i)) ≡[sym ∂₁-hom] ∂₁(sub x y) i ≡[cong e] ∂₁(∂₂c) i ≡[comp0] T₀
  --       ⟹ ⊕neg-zero 消去
  HR→R₁ : (x y : C₁) → HR x y → (i : Fin 3) → ∂₁ x i ≡ ∂₁ y i
  HR→R₁ x y (c , e) i = ⊕neg-zero (∂₁ x i) (∂₁ y i) (chain i)
    where
      chain : (j : Fin 3) → (∂₁ x j) ⊕ negate (∂₁ y j) ≡ T₀
      chain j =
        sym (∂₁-hom x y j)
        ∙ cong (λ w → ∂₁ w j) e
        ∙ cong (λ w → w j) (comp0-k3 c)

--------------------------------------------------------------------------------
-- §4 H₀ 侧关系桥（aug 形——与 FreeAbQuotient 的 R₀ = aug 相等 形对账）
--------------------------------------------------------------------------------

module K3H0
  (aug-hom : (x y : C₀) → aug (subᶠ x y) ≡ (aug x) ⊕ negate (aug y))
  where

  -- 单态别名（隐式钉参——元参教训）
  aug₀ : C₀ → Trit
  aug₀ w = aug w

  -- H₀ 侧同调关系（k=0：im ∂₁）
  HR₀ : C₀ → C₀ → Set
  HR₀ x y = Σ C₁ (λ b → subᶠ x y ≡ ∂₁ b)

  -- 关系桥（条件式）：HR₀ x y ⟹ aug x ≡ aug y（R₀ 形——FreeAbQuotient 的商关系）
  --   链：aug x ⊕ neg(aug y) ≡[sym aug-hom] aug(sub x y) ≡[cong e] aug(∂₁ b) ≡[aug-∂₁-zero] T₀
  HR0→R₀ : (x y : C₀) → HR₀ x y → aug x ≡ aug y
  HR0→R₀ x y (b , e) = ⊕neg-zero (aug x) (aug y) chain0
    where
      chain0 : (aug x) ⊕ negate (aug y) ≡ T₀
      chain0 =
        sym (aug-hom x y)
        ∙ (cong aug₀ e ∙ eqToPath (aug-∂₁-zero b))

--------------------------------------------------------------------------------
-- §5 立界（精确剩余）
--------------------------------------------------------------------------------
-- (i) comp0-k3 : ∂₁∘∂₂ = 0 具体证（接 MorseSqZero 线的 ∂²=0 件——
--     MorseBoundaryK3 的 ∂₁ᶜ 形与 FreeAbBoundary 的 ∂₁ 形对账后可接）；
-- (ii) ∂₁-hom / aug-hom 同态律具体证（Trit 点态 9 案 × 位置展开，~40-80 行）；
-- (iii) Hₖ 群律（transport-of-structure 同 FreeAbQuotient 的 +H₀ 先例）；
-- (iv) HRWells 实例化（等价三律 + hr-resp 同余——subᶠ 的群律面）。
-- 核对锚：H₀ = C₀/HR₀ ≅ Trit（f₀ 先例）/ H₁ = C₁/HR ↔ R₁ 代数形（§3 桥）
--         / H₂ = ker ∂₂（∂₂ 单射形——FreeAbHomologyGroup h₂-zero 先例）。
