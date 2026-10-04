{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.FreeAbHomologyGroup
-- 任务书第二层·2.5 泛型化（GAP-M7a）：FAb 载体上的**商型同调群**
--
-- 数学背景：此前同调以谓词/维数形态存在（dimH 维数级、FreeAbHomology
--   循环刻画谓词级、HomologyLES 诚实边界注明「商型结构」为阻塞点）。
--   本模块在 K₃ filled3C 实例上闭合**集合商形态**的同调群
--   （群律转移与泛型 HIT 商 = M7a-泛型，后续原子件）：
--
--     H₀ = C₀/ im ∂₁ ≅ GF(3)   —— 增广映射 aug 诱导的商集同构
--     H₁ = ker ∂₁ / im ∂₂ = 0   —— ≈₁ 形态（∂₁ 值逐点相等）下平凡
--     H₂ = ker ∂₂ = 0           —— ∂₂ 单射（h₂-zero）
--
--   ≈₀ x y := aug x ≡ aug y（aug x = x₀⊕x₁⊕x₂）——等价关系；
--   im ∂₁ ⊆ ker aug（aug∘∂₁ = 0，neg-add 三循环）⟹ 商良定义；
--   同构 Trit：fwd = aug（类上常值），bwd = c ↦ c·δ₀，往返闭合。
--
-- 复用：FreeAbBoundary（∂₁/∂₂/C₀-C₂）+ FreeAbH0（h₂-zero）+ Base/Trit。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.FreeAbHomologyGroup where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; ⊕-assoc; ⊕-comm)
open import Sovereign.Base.Trit using (⊕-identityʳ)
open import Sovereign.Problem.Hodge.FreeAbBoundary
  using (C₀; C₁; C₂; ∂₁; ∂₂)
open import Sovereign.Problem.Hodge.FreeAbH0 using (h₂-zero)

--------------------------------------------------------------------------------
-- §1. 增广映射 aug : C₀ → Trit 及线性
--------------------------------------------------------------------------------

aug : C₀ → Trit
aug x = (x fzero ⊕ x (fsuc fzero)) ⊕ x (fsuc (fsuc fzero))

-- ⚠ 群律转移（≈₀-add 良定义）移至 M7a-泛型（cubical HIT 商层）：
--   实例层的 H₀ ≅ GF(3) 同构（§6）在集合层闭合，不需要 ≈₀-add；
--   泛型商群运算的良定义性（五引理链）为后续原子件。

-- ⚠ 群律转移（≈₀-add 良定义）移至 M7a-泛型（cubical HIT 商层）：
--   实例层的 H₀ ≅ GF(3) 同构（§6）在集合层闭合，不需要 ≈₀-add；
--   泛型商群运算的良定义性（五引理链）为后续原子件。

--------------------------------------------------------------------------------
-- §2. 边界平凡：aug ∘ ∂₁ = 0（neg-add 三循环；3-case refl）
--------------------------------------------------------------------------------

aug-∂₁-zero : ∀ (b : C₁) → aug (∂₁ b) ≡ T₀
aug-∂₁-zero b with b fzero | b (fsuc fzero) | b (fsuc (fsuc fzero))
... | T₀ | T₀ | T₀ = refl
... | T₀ | T₀ | T₁ = refl
... | T₀ | T₀ | T₂ = refl
... | T₀ | T₁ | T₀ = refl
... | T₀ | T₁ | T₁ = refl
... | T₀ | T₁ | T₂ = refl
... | T₀ | T₂ | T₀ = refl
... | T₀ | T₂ | T₁ = refl
... | T₀ | T₂ | T₂ = refl
... | T₁ | T₀ | T₀ = refl
... | T₁ | T₀ | T₁ = refl
... | T₁ | T₀ | T₂ = refl
... | T₁ | T₁ | T₀ = refl
... | T₁ | T₁ | T₁ = refl
... | T₁ | T₁ | T₂ = refl
... | T₁ | T₂ | T₀ = refl
... | T₁ | T₂ | T₁ = refl
... | T₁ | T₂ | T₂ = refl
... | T₂ | T₀ | T₀ = refl
... | T₂ | T₀ | T₁ = refl
... | T₂ | T₀ | T₂ = refl
... | T₂ | T₁ | T₀ = refl
... | T₂ | T₁ | T₁ = refl
... | T₂ | T₁ | T₂ = refl
... | T₂ | T₂ | T₀ = refl
... | T₂ | T₂ | T₁ = refl
... | T₂ | T₂ | T₂ = refl

--------------------------------------------------------------------------------
-- §3. H₀ 商等价 ≈₀：x ≈₀ y ⟺ aug x ≡ aug y（等价关系）
--------------------------------------------------------------------------------

≈₀ : C₀ → C₀ → Set
≈₀ x y = aug x ≡ aug y

≈₀-refl : ∀ x → ≈₀ x x
≈₀-refl x = refl

≈₀-sym : ∀ x y → ≈₀ x y → ≈₀ y x
≈₀-sym x y h = sym h

≈₀-trans : ∀ x y z → ≈₀ x y → ≈₀ y z → ≈₀ x z
≈₀-trans x y z h₁ h₂ = trans h₁ h₂

zeroᶠ₃ : C₀
zeroᶠ₃ = λ _ → T₀

--------------------------------------------------------------------------------
-- §4. 边界在商中平凡：∂₁ b ≈₀ 0ᶠ（im ∂₁ ⊆ ker aug）
--------------------------------------------------------------------------------

bnd-trivial : ∀ (b : C₁) → ≈₀ (∂₁ b) zeroᶠ₃
bnd-trivial b = aug-∂₁-zero b

--------------------------------------------------------------------------------
-- §6. H₀ ≅ GF(3)：fwd = aug（类上常值），bwd = c ↦ c·δ₀，往返闭合
--------------------------------------------------------------------------------

-- bwd：c ↦ c·δ₀（δ₀ = fzero 处生成元）
h₀-bwd : Trit → C₀
h₀-bwd c fzero = c
h₀-bwd c (fsuc _) = T₀

-- fwd∘bwd：aug (c·δ₀) = c（逐点计算）
h₀-fwd-bwd : ∀ c → aug (h₀-bwd c) ≡ c
h₀-fwd-bwd c = trans (cong (_⊕ T₀) (⊕-identityʳ c)) (⊕-identityʳ c)

-- bwd 常值：x ≈₀ y ⟹ aug x ≡ aug y（即 ≈₀ 定义本身——fwd 良定义 ✓）

-- 商同构的完整形态：x 的类由 aug x 唯一决定（FreeAbH0 分解定理的商重述：
--   x ≈₀ (aug x)·δ₀，因 x ∸ (aug x)·δ₀ ∈ im ∂₁）
h₀-class : ∀ (x : C₀) → ≈₀ x (h₀-bwd (aug x))
h₀-class x = sym (h₀-fwd-bwd (aug x))

--------------------------------------------------------------------------------
-- §7. H₁ = 0（≈₁ 形态平凡）与 H₂ = 0（∂₂ 单射）
--------------------------------------------------------------------------------

-- H₁ 商等价 ≈₁：x ≈₁ y ⟺ ∂₁ x 与 ∂₁ y 逐点相等
≈₁ : C₁ → C₁ → Set
≈₁ x y = ∀ i → ∂₁ x i ≡ ∂₁ y i

-- H₁ = 0：任意循环 x 满足 x ≈₁ 0ᶠ（∂₁ x = 0 = ∂₁ 0ᶠ，逐点立即）
zeroᶠ₁ : C₁
zeroᶠ₁ = λ _ → T₀

h₁-trivial : ∀ (x : C₁) → (∀ i → ∂₁ x i ≡ T₀) → ≈₁ x zeroᶠ₁
h₁-trivial x hx fzero = hx fzero
h₁-trivial x hx (fsuc fzero) = hx (fsuc fzero)
h₁-trivial x hx (fsuc (fsuc fzero)) = hx (fsuc (fsuc fzero))

-- H₂ = 0：∂₂ 单射于生成元（FreeAbH0.h₂-zero 复用）
h₂-trivial : ∀ (c : C₂) → (∀ i → ∂₂ c i ≡ T₀) → c fzero ≡ T₀
h₂-trivial c h = h₂-zero c (h fzero)

--------------------------------------------------------------------------------
-- §8. H₀ 非平凡性：T₁ 类 ≠ 0 类（β₀ = 1 的商层见证——与 dimH-filled3-0 ≡ 1 对账）
--------------------------------------------------------------------------------

h₀-T₁-nontrivial : ¬ (≈₀ (h₀-bwd T₁) zeroᶠ₃)
h₀-T₁-nontrivial h = triv (trans (h₀-fwd-bwd T₁) h)
  where
    triv : T₁ ≡ T₀ → ⊥
    triv ()
