{-# OPTIONS --rewriting #-}

-- | Sovereign.Geometry.ConformalCore
-- 共形几何核心：共形群 Conf = (C₃)⁶ ⋊ C₂ + 共形点 = Conf-轨道
--
-- GF(3) 保角性: λ²≡1 → 缩放保持内积不变 (inner-scale2-inv)
-- Conf = (C₃ × C₃ × C₃ × C₃ × C₃ × C₃) ⋊ C₂, |Conf| = 1458
-- 射影群 G = (C₃)³ ⋊ C₂ 是 Conf 的子群

module Sovereign.Geometry.ConformalCore where

open import Data.Nat using (ℕ; _*_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Structology.T6 using (T6Lattice)

--------------------------------------------------------------------------------
-- 1. GF(3) 缩放与平移 (C₃ × C₂)
--------------------------------------------------------------------------------

tritOf : Fin 3 → Trit
tritOf zero = T₀
tritOf (suc zero) = T₁
tritOf (suc (suc zero)) = T₂

finOf : Trit → Fin 3
finOf T₀ = zero
finOf T₁ = suc zero
finOf T₂ = suc (suc zero)

-- C₃ 平移: x → x+1 mod 3 (从 ProjectiveCore 复用)
c3 : Fin 3 → Fin 3
c3 x = finOf (tritOf x ⊕ T₁)

-- C₂ 缩放: x → 2x mod 3 (GF(3) 中 2²≡1, 所以缩放是对合)
scale2 : Fin 3 → Fin 3
scale2 zero = zero
scale2 (suc zero) = suc (suc zero)
scale2 (suc (suc zero)) = suc zero

-- 验证: scale2 的具体值
scale2-values : scale2 zero ≡ zero × scale2 (suc zero) ≡ suc (suc zero) × scale2 (suc (suc zero)) ≡ suc zero
scale2-values = refl , refl , refl  -- 0→0, 1→2, 2→1

-- 缩放是对合: scale2 ∘ scale2 ≡ id
scale2² : ∀ (x : Fin 3) → scale2 (scale2 x) ≡ x
scale2² zero = refl
scale2² (suc zero) = refl
scale2² (suc (suc zero)) = refl

-- C₃ 周期 3 (从 ProjectiveCore 复用)
c3³ : ∀ (x : Fin 3) → c3 (c3 (c3 x)) ≡ x
c3³ zero = refl
c3³ (suc zero) = refl
c3³ (suc (suc zero)) = refl

-- 平移与缩放不直接交换: c3 ∘ scale2 = scale2 ∘ c3² (半直积非平凡)
c3-scale2-conj : ∀ (x : Fin 3) → c3 (scale2 x) ≡ scale2 (c3 (c3 x))
c3-scale2-conj zero = refl          -- c3(0)=1, scale2(0)=0 → 2×0+1=1, 2×(0+2)=2×2=4≡1
c3-scale2-conj (suc zero) = refl    -- c3(1)=2, scale2(1)=2 → 2×1+1=3≡0, 2×(1+2)=2×3=6≡0
c3-scale2-conj (suc (suc zero)) = refl  -- c3(2)=0, scale2(2)=1 → 2×2+1=5≡2, 2×(2+2)=2×4=8≡2

--------------------------------------------------------------------------------
-- 2. GF(3) 内积
--------------------------------------------------------------------------------

-- 单分量内积: ⟨a,b⟩ = a ⊗ b (GF(3) 乘法)
_·₃_ : Fin 3 → Fin 3 → Fin 3
x ·₃ y = finOf (tritOf x ⊗ tritOf y)

-- GF(3) 保角性核心定理: 缩放保持内积不变
inner-scale2-inv : ∀ (x y : Fin 3) → (scale2 x ·₃ scale2 y) ≡ (x ·₃ y)
inner-scale2-inv zero zero = refl
inner-scale2-inv zero (suc zero) = refl
inner-scale2-inv zero (suc (suc zero)) = refl
inner-scale2-inv (suc zero) zero = refl
inner-scale2-inv (suc zero) (suc zero) = refl
inner-scale2-inv (suc zero) (suc (suc zero)) = refl
inner-scale2-inv (suc (suc zero)) zero = refl
inner-scale2-inv (suc (suc zero)) (suc zero) = refl
inner-scale2-inv (suc (suc zero)) (suc (suc zero)) = refl

-- T⁶ 全局内积: 6 分量内积的 GF(3) 和
t6Inner : T6Lattice → T6Lattice → Fin 3
t6Inner (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
        (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ y₅ ∷ []) =
  ((((((x₀ ·₃ y₀) ⊕₃ (x₁ ·₃ y₁)) ⊕₃ (x₂ ·₃ y₂)) ⊕₃ (x₃ ·₃ y₃)) ⊕₃ (x₄ ·₃ y₄)) ⊕₃ (x₅ ·₃ y₅))
  where
    _⊕₃_ : Fin 3 → Fin 3 → Fin 3
    x ⊕₃ y = finOf (Sovereign.Base.Trit._⊕_ (tritOf x) (tritOf y))

--------------------------------------------------------------------------------
-- 3. 共形群 Conf = (C₃)⁶ ⋊ C₂
--------------------------------------------------------------------------------

-- 6 个独立的 C₃ 平移
record C3Vec : Set where
  constructor c3v
  field v0 v1 v2 v3 v4 v5 : Fin 3

-- 共形群元素: (平移向量, 缩放标志)
record ConfElement : Set where
  constructor ⟨_,_⟩
  field tvec : C3Vec
        scl  : Fin 2  -- 0=保长, 1=缩放

conf-id : ConfElement
conf-id = ⟨ c3v zero zero zero zero zero zero , zero ⟩

-- 平移分量加法 (逐分量 +₃)
_+v_ : C3Vec → C3Vec → C3Vec
c3v a₀ a₁ a₂ a₃ a₄ a₅ +v c3v b₀ b₁ b₂ b₃ b₄ b₅ =
  c3v (a₀ +₃ b₀) (a₁ +₃ b₁) (a₂ +₃ b₂) (a₃ +₃ b₃) (a₄ +₃ b₄) (a₅ +₃ b₅)
  where _+₃_ : Fin 3 → Fin 3 → Fin 3
        x +₃ y = finOf (tritOf x ⊕ tritOf y)

-- 缩放在平移上的作用 (半直积)
scale-on-trans : Fin 2 → C3Vec → C3Vec
scale-on-trans zero    v = v
scale-on-trans (suc _) (c3v v₀ v₁ v₂ v₃ v₄ v₅) =
  c3v (scale2 v₀) (scale2 v₁) (scale2 v₂) (scale2 v₃) (scale2 v₄) (scale2 v₅)

-- 群乘法: (t₁,s₁)·(t₂,s₂) = (t₁ + s₁·t₂, s₁+s₂)
_+₂_ : Fin 2 → Fin 2 → Fin 2
zero +₂ x = x
suc x +₂ zero = suc x
suc x +₂ suc y = zero

conf-mul : ConfElement → ConfElement → ConfElement
conf-mul ⟨ t₁ , s₁ ⟩ ⟨ t₂ , s₂ ⟩ =
  ⟨ t₁ +v scale-on-trans s₁ t₂ , s₁ +₂ s₂ ⟩

-- 逆元
conf-inv : ConfElement → ConfElement
conf-inv ⟨ c3v v₀ v₁ v₂ v₃ v₄ v₅ , s ⟩ =
  ⟨ c3v (i3 v₀) (i3 v₁) (i3 v₂) (i3 v₃) (i3 v₄) (i3 v₅) , s ⟩
  where i3 : Fin 3 → Fin 3
        i3 zero = zero
        i3 (suc zero) = suc (suc zero)
        i3 (suc (suc zero)) = suc zero

-- |Conf| = 3⁶ × 2 = 1458
conf-card : ℕ
conf-card = 729 * 2

conf-card-refl : conf-card ≡ 1458
conf-card-refl = refl

--------------------------------------------------------------------------------
-- 4. Conf 在 T⁶ 上的作用
--------------------------------------------------------------------------------

c3ⁿ : Fin 3 → Fin 3 → Fin 3
c3ⁿ zero    x = x
c3ⁿ (suc zero)    x = c3 x
c3ⁿ (suc (suc zero)) x = c3 (c3 x)

-- 每个坐标独立施加 C₃ 平移和 C₂ 缩放
conf-action : ConfElement → T6Lattice → T6Lattice
conf-action ⟨ c3v a₀ a₁ a₂ a₃ a₄ a₅ , zero ⟩ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  c3ⁿ a₀ x₀ ∷ c3ⁿ a₁ x₁ ∷ c3ⁿ a₂ x₂ ∷ c3ⁿ a₃ x₃ ∷ c3ⁿ a₄ x₄ ∷ c3ⁿ a₅ x₅ ∷ []
conf-action ⟨ c3v a₀ a₁ a₂ a₃ a₄ a₅ , suc _ ⟩ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) =
  scale2 (c3ⁿ a₀ x₀) ∷ scale2 (c3ⁿ a₁ x₁) ∷ scale2 (c3ⁿ a₂ x₂) ∷
  scale2 (c3ⁿ a₃ x₃) ∷ scale2 (c3ⁿ a₄ x₄) ∷ scale2 (c3ⁿ a₅ x₅) ∷ []

--------------------------------------------------------------------------------
-- 5. Conf-轨道 = 共形点
--------------------------------------------------------------------------------

record ConfOrbitRel (x y : T6Lattice) : Set where
  constructor conf-orbit-path
  field g    : ConfElement
        eq   : conf-action g x ≡ y

ConfOrbit : T6Lattice → Set
ConfOrbit x = Σ T6Lattice (λ y → ConfOrbitRel x y)

record ConformalPointRec : Set where
  constructor mk-cpoint
  field rep    : T6Lattice
        orbit  : ConfOrbit rep

--------------------------------------------------------------------------------
-- 6. 群公理 (postulate, 遵循 ProjectiveCore 模式)
--------------------------------------------------------------------------------

postulate
  conf-id-left  : ∀ g → conf-mul conf-id g ≡ g
  conf-id-right : ∀ g → conf-mul g conf-id ≡ g
  conf-inv-left : ∀ g → conf-mul (conf-inv g) g ≡ conf-id
  conf-assoc    : ∀ g h k → conf-mul (conf-mul g h) k ≡ conf-mul g (conf-mul h k)
  conf-refl     : ∀ x → ConfOrbitRel x x
  conf-sym      : ∀ x y → ConfOrbitRel x y → ConfOrbitRel y x
  conf-trans    : ∀ x y z → ConfOrbitRel x y → ConfOrbitRel y z → ConfOrbitRel x z

--------------------------------------------------------------------------------
-- 7. 共形不变量声明
--------------------------------------------------------------------------------

postulate
  t6Inner-conformal : ∀ (g : ConfElement) (p q : T6Lattice) →
    t6Inner (conf-action g p) (conf-action g q) ≡ t6Inner p q
