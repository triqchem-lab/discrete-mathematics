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
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Synthesis.T6 using (T6Lattice)

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
_⊕₃_ : Fin 3 → Fin 3 → Fin 3
x ⊕₃ y = finOf (Sovereign.Base.Trit._⊕_ (tritOf x) (tritOf y))

t6Inner : T6Lattice → T6Lattice → Fin 3
t6Inner (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
        (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ y₅ ∷ []) =
  ((((((x₀ ·₃ y₀) ⊕₃ (x₁ ·₃ y₁)) ⊕₃ (x₂ ·₃ y₂)) ⊕₃ (x₃ ·₃ y₃)) ⊕₃ (x₄ ·₃ y₄)) ⊕₃ (x₅ ·₃ y₅))

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
_+₃_ : Fin 3 → Fin 3 → Fin 3
x +₃ y = finOf (tritOf x ⊕ tritOf y)

_+v_ : C3Vec → C3Vec → C3Vec
c3v a₀ a₁ a₂ a₃ a₄ a₅ +v c3v b₀ b₁ b₂ b₃ b₄ b₅ =
  c3v (a₀ +₃ b₀) (a₁ +₃ b₁) (a₂ +₃ b₂) (a₃ +₃ b₃) (a₄ +₃ b₄) (a₅ +₃ b₅)

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
neg3 : Fin 3 → Fin 3
neg3 zero = zero
neg3 (suc zero) = suc (suc zero)
neg3 (suc (suc zero)) = suc zero

neg3-invol : ∀ x → neg3 (neg3 x) ≡ x
neg3-invol zero = refl
neg3-invol (suc zero) = refl
neg3-invol (suc (suc zero)) = refl

neg-v : C3Vec → C3Vec
neg-v (c3v v₀ v₁ v₂ v₃ v₄ v₅) =
  c3v (neg3 v₀) (neg3 v₁) (neg3 v₂) (neg3 v₃) (neg3 v₄) (neg3 v₅)

-- [勘正 2026-10-11] semidirect 真逆：inv⟨t,s⟩ = ⟨neg-v (scale-on-trans s t), s⟩
-- （原形 ⟨neg-v t, s⟩ 漏 scale——conf-inv-left 于 s=1,t≠0 为假（statement_wrong 案）；
--   s=1 时元素自逆：(t,1)² = (t + scale2 t, 0) = (t + neg t, 0) = id）
conf-inv : ConfElement → ConfElement
conf-inv ⟨ tvec , s ⟩ = ⟨ neg-v (scale-on-trans s tvec) , s ⟩

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

-- §6 群公理与轨道等价律（构造性——原 postulate 全消）
-- 策略：Fin 闭计算 + 仿射族见证（scale2^s∘c3^t 族对复合封闭——c3-scale2-conj 承载）
-- 口径：豁免精化判据正解——群公理=结构公理、等价律=可导出件，零豁免

cv-ext : ∀ {v₀ v₀′ v₁ v₁′ v₂ v₂′ v₃ v₃′ v₄ v₄′ v₅ v₅′ : Fin 3}
   → v₀ ≡ v₀′ → v₁ ≡ v₁′ → v₂ ≡ v₂′ → v₃ ≡ v₃′ → v₄ ≡ v₄′ → v₅ ≡ v₅′
   → c3v v₀ v₁ v₂ v₃ v₄ v₅ ≡ c3v v₀′ v₁′ v₂′ v₃′ v₄′ v₅′
cv-ext refl refl refl refl refl refl = refl

+₃-zeroˡ : ∀ x → zero +₃ x ≡ x
+₃-zeroˡ zero = refl
+₃-zeroˡ (suc zero) = refl
+₃-zeroˡ (suc (suc zero)) = refl

+₃-zeroʳ : ∀ x → x +₃ zero ≡ x
+₃-zeroʳ zero = refl
+₃-zeroʳ (suc zero) = refl
+₃-zeroʳ (suc (suc zero)) = refl

+₃-assoc : ∀ x y z → (x +₃ y) +₃ z ≡ x +₃ (y +₃ z)
+₃-assoc zero zero zero = refl
+₃-assoc zero zero (suc zero) = refl
+₃-assoc zero zero (suc (suc zero)) = refl
+₃-assoc zero (suc zero) zero = refl
+₃-assoc zero (suc zero) (suc zero) = refl
+₃-assoc zero (suc zero) (suc (suc zero)) = refl
+₃-assoc zero (suc (suc zero)) zero = refl
+₃-assoc zero (suc (suc zero)) (suc zero) = refl
+₃-assoc zero (suc (suc zero)) (suc (suc zero)) = refl
+₃-assoc (suc zero) zero zero = refl
+₃-assoc (suc zero) zero (suc zero) = refl
+₃-assoc (suc zero) zero (suc (suc zero)) = refl
+₃-assoc (suc zero) (suc zero) zero = refl
+₃-assoc (suc zero) (suc zero) (suc zero) = refl
+₃-assoc (suc zero) (suc zero) (suc (suc zero)) = refl
+₃-assoc (suc zero) (suc (suc zero)) zero = refl
+₃-assoc (suc zero) (suc (suc zero)) (suc zero) = refl
+₃-assoc (suc zero) (suc (suc zero)) (suc (suc zero)) = refl
+₃-assoc (suc (suc zero)) zero zero = refl
+₃-assoc (suc (suc zero)) zero (suc zero) = refl
+₃-assoc (suc (suc zero)) zero (suc (suc zero)) = refl
+₃-assoc (suc (suc zero)) (suc zero) zero = refl
+₃-assoc (suc (suc zero)) (suc zero) (suc zero) = refl
+₃-assoc (suc (suc zero)) (suc zero) (suc (suc zero)) = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) zero = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) (suc zero) = refl
+₃-assoc (suc (suc zero)) (suc (suc zero)) (suc (suc zero)) = refl

+₃-negˡ : ∀ x → neg3 x +₃ x ≡ zero
+₃-negˡ zero = refl
+₃-negˡ (suc zero) = refl
+₃-negˡ (suc (suc zero)) = refl

+₃-negʳ : ∀ x → x +₃ neg3 x ≡ zero
+₃-negʳ zero = refl
+₃-negʳ (suc zero) = refl
+₃-negʳ (suc (suc zero)) = refl

+ᵥ-zeroˡ : ∀ v → (c3v zero zero zero zero zero zero +v v) ≡ v
+ᵥ-zeroˡ (c3v v₀ v₁ v₂ v₃ v₄ v₅) =
  cv-ext (+₃-zeroˡ v₀) (+₃-zeroˡ v₁) (+₃-zeroˡ v₂) (+₃-zeroˡ v₃) (+₃-zeroˡ v₄) (+₃-zeroˡ v₅)

+ᵥ-zeroʳ : ∀ v → (v +v c3v zero zero zero zero zero zero) ≡ v
+ᵥ-zeroʳ (c3v v₀ v₁ v₂ v₃ v₄ v₅) =
  cv-ext (+₃-zeroʳ v₀) (+₃-zeroʳ v₁) (+₃-zeroʳ v₂) (+₃-zeroʳ v₃) (+₃-zeroʳ v₄) (+₃-zeroʳ v₅)

+ᵥ-negˡ : ∀ v → (neg-v v +v v) ≡ c3v zero zero zero zero zero zero
+ᵥ-negˡ (c3v v₀ v₁ v₂ v₃ v₄ v₅) =
  cv-ext (+₃-negˡ v₀) (+₃-negˡ v₁) (+₃-negˡ v₂) (+₃-negˡ v₃) (+₃-negˡ v₄) (+₃-negˡ v₅)

+ᵥ-assoc : ∀ a b c → ((a +v b) +v c) ≡ (a +v (b +v c))
+ᵥ-assoc (c3v a₀ a₁ a₂ a₃ a₄ a₅) (c3v b₀ b₁ b₂ b₃ b₄ b₅) (c3v c₀ c₁ c₂ c₃ c₄ c₅) =
  cv-ext (+₃-assoc a₀ b₀ c₀) (+₃-assoc a₁ b₁ c₁) (+₃-assoc a₂ b₂ c₂)
        (+₃-assoc a₃ b₃ c₃) (+₃-assoc a₄ b₄ c₄) (+₃-assoc a₅ b₅ c₅)

+₂-zeroʳ : ∀ s → s +₂ zero ≡ s
+₂-zeroʳ zero = refl
+₂-zeroʳ (suc zero) = refl

+₂-self : ∀ s → s +₂ s ≡ zero
+₂-self zero = refl
+₂-self (suc zero) = refl

+₂-assoc : ∀ x y z → (x +₂ y) +₂ z ≡ x +₂ (y +₂ z)
+₂-assoc zero zero zero = refl
+₂-assoc zero zero (suc zero) = refl
+₂-assoc zero (suc zero) zero = refl
+₂-assoc zero (suc zero) (suc zero) = refl
+₂-assoc (suc zero) zero zero = refl
+₂-assoc (suc zero) zero (suc zero) = refl
+₂-assoc (suc zero) (suc zero) zero = refl
+₂-assoc (suc zero) (suc zero) (suc zero) = refl

scale2-+₃ : ∀ x y → scale2 (x +₃ y) ≡ scale2 x +₃ scale2 y
scale2-+₃ zero zero = refl
scale2-+₃ zero (suc zero) = refl
scale2-+₃ zero (suc (suc zero)) = refl
scale2-+₃ (suc zero) zero = refl
scale2-+₃ (suc zero) (suc zero) = refl
scale2-+₃ (suc zero) (suc (suc zero)) = refl
scale2-+₃ (suc (suc zero)) zero = refl
scale2-+₃ (suc (suc zero)) (suc zero) = refl
scale2-+₃ (suc (suc zero)) (suc (suc zero)) = refl

scale-dist-v : ∀ s a b → scale-on-trans s (a +v b) ≡ (scale-on-trans s a +v scale-on-trans s b)
scale-dist-v zero (c3v a₀ a₁ a₂ a₃ a₄ a₅) (c3v b₀ b₁ b₂ b₃ b₄ b₅) =
  cv-ext refl refl refl refl refl refl
scale-dist-v (suc zero) (c3v a₀ a₁ a₂ a₃ a₄ a₅) (c3v b₀ b₁ b₂ b₃ b₄ b₅) =
  cv-ext (scale2-+₃ a₀ b₀) (scale2-+₃ a₁ b₁) (scale2-+₃ a₂ b₂)
        (scale2-+₃ a₃ b₃) (scale2-+₃ a₄ b₄) (scale2-+₃ a₅ b₅)

scale-zero : ∀ s → scale-on-trans s (c3v zero zero zero zero zero zero) ≡ c3v zero zero zero zero zero zero
scale-zero zero = refl
scale-zero (suc zero) = cv-ext refl refl refl refl refl refl

scale-comp : ∀ s₁ s₂ v → scale-on-trans (s₁ +₂ s₂) v ≡ scale-on-trans s₁ (scale-on-trans s₂ v)
scale-comp zero zero (c3v v₀ v₁ v₂ v₃ v₄ v₅) = cv-ext refl refl refl refl refl refl
scale-comp zero (suc zero) (c3v v₀ v₁ v₂ v₃ v₄ v₅) = cv-ext refl refl refl refl refl refl
scale-comp (suc zero) zero (c3v v₀ v₁ v₂ v₃ v₄ v₅) = cv-ext refl refl refl refl refl refl
scale-comp (suc zero) (suc zero) (c3v v₀ v₁ v₂ v₃ v₄ v₅) =
  cv-ext (sym (scale2² v₀)) (sym (scale2² v₁)) (sym (scale2² v₂)) (sym (scale2² v₃)) (sym (scale2² v₄)) (sym (scale2² v₅))

c3ⁿ-add : ∀ a b x → c3ⁿ (a +₃ b) x ≡ c3ⁿ a (c3ⁿ b x)
c3ⁿ-add zero zero zero = refl
c3ⁿ-add zero zero (suc zero) = refl
c3ⁿ-add zero zero (suc (suc zero)) = refl
c3ⁿ-add zero (suc zero) zero = refl
c3ⁿ-add zero (suc zero) (suc zero) = refl
c3ⁿ-add zero (suc zero) (suc (suc zero)) = refl
c3ⁿ-add zero (suc (suc zero)) zero = refl
c3ⁿ-add zero (suc (suc zero)) (suc zero) = refl
c3ⁿ-add zero (suc (suc zero)) (suc (suc zero)) = refl
c3ⁿ-add (suc zero) zero zero = refl
c3ⁿ-add (suc zero) zero (suc zero) = refl
c3ⁿ-add (suc zero) zero (suc (suc zero)) = refl
c3ⁿ-add (suc zero) (suc zero) zero = refl
c3ⁿ-add (suc zero) (suc zero) (suc zero) = refl
c3ⁿ-add (suc zero) (suc zero) (suc (suc zero)) = refl
c3ⁿ-add (suc zero) (suc (suc zero)) zero = refl
c3ⁿ-add (suc zero) (suc (suc zero)) (suc zero) = refl
c3ⁿ-add (suc zero) (suc (suc zero)) (suc (suc zero)) = refl
c3ⁿ-add (suc (suc zero)) zero zero = refl
c3ⁿ-add (suc (suc zero)) zero (suc zero) = refl
c3ⁿ-add (suc (suc zero)) zero (suc (suc zero)) = refl
c3ⁿ-add (suc (suc zero)) (suc zero) zero = refl
c3ⁿ-add (suc (suc zero)) (suc zero) (suc zero) = refl
c3ⁿ-add (suc (suc zero)) (suc zero) (suc (suc zero)) = refl
c3ⁿ-add (suc (suc zero)) (suc (suc zero)) zero = refl
c3ⁿ-add (suc (suc zero)) (suc (suc zero)) (suc zero) = refl
c3ⁿ-add (suc (suc zero)) (suc (suc zero)) (suc (suc zero)) = refl

c3ⁿ-inv : ∀ a x → c3ⁿ (neg3 a) (c3ⁿ a x) ≡ x
c3ⁿ-inv zero zero = refl
c3ⁿ-inv zero (suc zero) = refl
c3ⁿ-inv zero (suc (suc zero)) = refl
c3ⁿ-inv (suc zero) zero = refl
c3ⁿ-inv (suc zero) (suc zero) = refl
c3ⁿ-inv (suc zero) (suc (suc zero)) = refl
c3ⁿ-inv (suc (suc zero)) zero = refl
c3ⁿ-inv (suc (suc zero)) (suc zero) = refl
c3ⁿ-inv (suc (suc zero)) (suc (suc zero)) = refl

scale2-c3ⁿ : ∀ a x → scale2 (c3ⁿ a x) ≡ c3ⁿ (neg3 a) (scale2 x)
scale2-c3ⁿ zero zero = refl
scale2-c3ⁿ zero (suc zero) = refl
scale2-c3ⁿ zero (suc (suc zero)) = refl
scale2-c3ⁿ (suc zero) zero = refl
scale2-c3ⁿ (suc zero) (suc zero) = refl
scale2-c3ⁿ (suc zero) (suc (suc zero)) = refl
scale2-c3ⁿ (suc (suc zero)) zero = refl
scale2-c3ⁿ (suc (suc zero)) (suc zero) = refl
scale2-c3ⁿ (suc (suc zero)) (suc (suc zero)) = refl

-- 群公理
conf-id-left : ∀ g → conf-mul conf-id g ≡ g
conf-id-left ⟨ c3v v₀ v₁ v₂ v₃ v₄ v₅ , s ⟩ =
  cong₂ ⟨_,_⟩ (+ᵥ-zeroˡ (c3v v₀ v₁ v₂ v₃ v₄ v₅)) refl

conf-id-right : ∀ g → conf-mul g conf-id ≡ g
conf-id-right ⟨ t , s ⟩ =
  cong₂ ⟨_,_⟩ (trans (+ᵥ-cong (scale-zero s)) (+ᵥ-zeroʳ t)) (+₂-zeroʳ s)
  where
  +ᵥ-cong : ∀ {a b} → a ≡ b → (t +v a) ≡ (t +v b)
  +ᵥ-cong refl = refl

conf-inv-left : ∀ g → conf-mul (conf-inv g) g ≡ conf-id
conf-inv-left ⟨ c3v v₀ v₁ v₂ v₃ v₄ v₅ , zero ⟩ =
  cong₂ ⟨_,_⟩ (+ᵥ-negˡ (c3v v₀ v₁ v₂ v₃ v₄ v₅)) refl
conf-inv-left ⟨ c3v v₀ v₁ v₂ v₃ v₄ v₅ , suc zero ⟩ =
  cong₂ ⟨_,_⟩
    (+ᵥ-negˡ (c3v (scale2 v₀) (scale2 v₁) (scale2 v₂) (scale2 v₃) (scale2 v₄) (scale2 v₅))) refl

conf-assoc : ∀ g h k → conf-mul (conf-mul g h) k ≡ conf-mul g (conf-mul h k)
conf-assoc ⟨ t₁ , s₁ ⟩ ⟨ t₂ , s₂ ⟩ ⟨ t₃ , s₃ ⟩ =
  cong₂ ⟨_,_⟩
    (trans (+ᵥ-assoc t₁ (scale-on-trans s₁ t₂) (scale-on-trans (s₁ +₂ s₂) t₃))
      (cong (t₁ +v_)
        (trans (cong (λ z → scale-on-trans s₁ t₂ +v z) (scale-comp s₁ s₂ t₃))
          (sym (scale-dist-v s₁ t₂ (scale-on-trans s₂ t₃))))))
    (+₂-assoc s₁ s₂ s₃)

--------------------------------------------------------------------------------
-- 7. 共形不变量声明
--------------------------------------------------------------------------------

-- 轨道等价律（仿射族见证——c3-scale2-conj 承载共轭关系；等价律=可导出件）
tv6 : ∀ {x₀ x₀′ x₁ x₁′ x₂ x₂′ x₃ x₃′ x₄ x₄′ x₅ x₅′ : Fin 3}
   → x₀ ≡ x₀′ → x₁ ≡ x₁′ → x₂ ≡ x₂′ → x₃ ≡ x₃′ → x₄ ≡ x₄′ → x₅ ≡ x₅′
   → (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) ≡ (x₀′ ∷ x₁′ ∷ x₂′ ∷ x₃′ ∷ x₄′ ∷ x₅′ ∷ [])
tv6 refl refl refl refl refl refl = refl

conf-refl : ∀ x → ConfOrbitRel x x
conf-refl (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) = conf-orbit-path conf-id refl

conf-sym : ∀ x y → ConfOrbitRel x y → ConfOrbitRel y x
conf-sym (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) .(conf-action g (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []))
         (conf-orbit-path g refl) = help g
  where
  step : ∀ t x → scale2 (c3ⁿ t (scale2 (c3ⁿ t x))) ≡ x
  step t x = trans (cong (λ z → scale2 (c3ⁿ t z)) (scale2-c3ⁿ t x))
              (trans (cong scale2 mid) (scale2² x))
    where
    mid : c3ⁿ t (c3ⁿ (neg3 t) (scale2 x)) ≡ scale2 x
    mid = trans (sym (c3ⁿ-add t (neg3 t) (scale2 x)))
            (cong (λ z → c3ⁿ z (scale2 x)) (+₃-negʳ t))
  help : ∀ g → ConfOrbitRel (conf-action g (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []))
                            (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
  help ⟨ c3v a₀ a₁ a₂ a₃ a₄ a₅ , zero ⟩ =
    conf-orbit-path ⟨ c3v (neg3 a₀) (neg3 a₁) (neg3 a₂) (neg3 a₃) (neg3 a₄) (neg3 a₅) , zero ⟩
      (tv6 (c3ⁿ-inv a₀ x₀) (c3ⁿ-inv a₁ x₁) (c3ⁿ-inv a₂ x₂)
           (c3ⁿ-inv a₃ x₃) (c3ⁿ-inv a₄ x₄) (c3ⁿ-inv a₅ x₅))
  help ⟨ c3v a₀ a₁ a₂ a₃ a₄ a₅ , suc zero ⟩ =
    conf-orbit-path ⟨ c3v a₀ a₁ a₂ a₃ a₄ a₅ , suc zero ⟩
      (tv6 (step a₀ x₀) (step a₁ x₁) (step a₂ x₂) (step a₃ x₃) (step a₄ x₄) (step a₅ x₅))

conf-trans : ∀ x y z → ConfOrbitRel x y → ConfOrbitRel y z → ConfOrbitRel x z
conf-trans (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
           .(conf-action g₁ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []))
           .(conf-action g₂ (conf-action g₁ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])))
           (conf-orbit-path g₁ refl) (conf-orbit-path g₂ refl) = help g₂ g₁
  where
  step2 : ∀ t₂ t₁ x → scale2 (c3ⁿ t₂ (scale2 (c3ⁿ t₁ x))) ≡ c3ⁿ (neg3 (t₂ +₃ neg3 t₁)) x
  step2 t₂ t₁ x = trans (cong (λ z → scale2 (c3ⁿ t₂ z)) (scale2-c3ⁿ t₁ x))
    (trans (cong scale2 (sym (c3ⁿ-add t₂ (neg3 t₁) (scale2 x))))
      (trans (scale2-c3ⁿ (t₂ +₃ neg3 t₁) (scale2 x))
        (cong (c3ⁿ (neg3 (t₂ +₃ neg3 t₁))) (scale2² x))))
  step3 : ∀ t₂ t₁ x → scale2 (c3ⁿ (neg3 (t₂ +₃ neg3 t₁)) x) ≡ c3ⁿ t₂ (scale2 (c3ⁿ t₁ x))
  step3 t₂ t₁ x = trans (scale2-c3ⁿ (neg3 (t₂ +₃ neg3 t₁)) x)
    (trans (cong (λ z → c3ⁿ z (scale2 x)) (neg3-invol (t₂ +₃ neg3 t₁)))
      (sym (trans (cong (c3ⁿ t₂) (scale2-c3ⁿ t₁ x))
        (sym (c3ⁿ-add t₂ (neg3 t₁) (scale2 x))))))
  help : ∀ g₂ g₁ → ConfOrbitRel (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
        (conf-action g₂ (conf-action g₁ (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])))
  help ⟨ c3v a₂ b₂ k₂ d₂ e₂ f₂ , zero ⟩ ⟨ c3v a₁ b₁ k₁ d₁ e₁ f₁ , zero ⟩ =
    conf-orbit-path ⟨ c3v (a₂ +₃ a₁) (b₂ +₃ b₁) (k₂ +₃ k₁) (d₂ +₃ d₁) (e₂ +₃ e₁) (f₂ +₃ f₁) , zero ⟩
      (tv6 (c3ⁿ-add a₂ a₁ x₀) (c3ⁿ-add b₂ b₁ x₁) (c3ⁿ-add k₂ k₁ x₂)
           (c3ⁿ-add d₂ d₁ x₃) (c3ⁿ-add e₂ e₁ x₄) (c3ⁿ-add f₂ f₁ x₅))
  help ⟨ c3v a₂ b₂ k₂ d₂ e₂ f₂ , suc zero ⟩ ⟨ c3v a₁ b₁ k₁ d₁ e₁ f₁ , zero ⟩ =
    conf-orbit-path ⟨ c3v (a₂ +₃ a₁) (b₂ +₃ b₁) (k₂ +₃ k₁) (d₂ +₃ d₁) (e₂ +₃ e₁) (f₂ +₃ f₁) , suc zero ⟩
      (tv6 (cong scale2 (c3ⁿ-add a₂ a₁ x₀)) (cong scale2 (c3ⁿ-add b₂ b₁ x₁))
           (cong scale2 (c3ⁿ-add k₂ k₁ x₂)) (cong scale2 (c3ⁿ-add d₂ d₁ x₃))
           (cong scale2 (c3ⁿ-add e₂ e₁ x₄)) (cong scale2 (c3ⁿ-add f₂ f₁ x₅)))
  help ⟨ c3v a₂ b₂ k₂ d₂ e₂ f₂ , zero ⟩ ⟨ c3v a₁ b₁ k₁ d₁ e₁ f₁ , suc zero ⟩ =
    conf-orbit-path ⟨ c3v (neg3 (a₂ +₃ neg3 a₁)) (neg3 (b₂ +₃ neg3 b₁)) (neg3 (k₂ +₃ neg3 k₁))
                        (neg3 (d₂ +₃ neg3 d₁)) (neg3 (e₂ +₃ neg3 e₁)) (neg3 (f₂ +₃ neg3 f₁)) , suc zero ⟩
      (tv6 (step3 a₂ a₁ x₀) (step3 b₂ b₁ x₁) (step3 k₂ k₁ x₂)
           (step3 d₂ d₁ x₃) (step3 e₂ e₁ x₄) (step3 f₂ f₁ x₅))
  help ⟨ c3v a₂ b₂ k₂ d₂ e₂ f₂ , suc zero ⟩ ⟨ c3v a₁ b₁ k₁ d₁ e₁ f₁ , suc zero ⟩ =
    conf-orbit-path ⟨ c3v (neg3 (a₂ +₃ neg3 a₁)) (neg3 (b₂ +₃ neg3 b₁)) (neg3 (k₂ +₃ neg3 k₁))
                        (neg3 (d₂ +₃ neg3 d₁)) (neg3 (e₂ +₃ neg3 e₁)) (neg3 (f₂ +₃ neg3 f₁)) , zero ⟩
      (tv6 (sym (step2 a₂ a₁ x₀)) (sym (step2 b₂ b₁ x₁)) (sym (step2 k₂ k₁ x₂))
           (sym (step2 d₂ d₁ x₃)) (sym (step2 e₂ e₁ x₄)) (sym (step2 f₂ f₁ x₅)))

--------------------------------------------------------------------------------
-- §7 共形不变量（陈述勘正——原 t6Inner-conformal 为假，statement_wrong 案）
-- 原陈述「∀g p q · t6Inner (g·p) (g·q) ≡ t6Inner p q」对纯平移为反例（内积非平移不变）；
-- 真实共形部分 = 缩放不变性（inner-scale2-inv 承载）——以下两件替代：
--------------------------------------------------------------------------------

-- 真形：缩放分量保持 GF(3) 内积（共形性 = λ²≡1）
t6Inner-scale : ∀ (s : Fin 2) (p q : T6Lattice) →
  t6Inner (conf-action ⟨ c3v zero zero zero zero zero zero , s ⟩ p)
          (conf-action ⟨ c3v zero zero zero zero zero zero , s ⟩ q) ≡ t6Inner p q
t6Inner-scale zero (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ y₅ ∷ []) = refl
t6Inner-scale (suc zero) (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ y₅ ∷ []) =
  cong₂ _⊕₃_ (cong₂ _⊕₃_ (cong₂ _⊕₃_ (cong₂ _⊕₃_ (cong₂ _⊕₃_
    (inner-scale2-inv x₀ y₀) (inner-scale2-inv x₁ y₁)) (inner-scale2-inv x₂ y₂))
    (inner-scale2-inv x₃ y₃)) (inner-scale2-inv x₄ y₄)) (inner-scale2-inv x₅ y₅)

-- 反证件：原全称陈述为假（纯平移反例——p=0 向量 inner=0，平移 e₁ 后 inner=1）
t6Inner-not-conformal :
  (∀ (g : ConfElement) (p q : T6Lattice) →
    t6Inner (conf-action g p) (conf-action g q) ≡ t6Inner p q) → ⊥
t6Inner-not-conformal hyp = contra (hyp ⟨ c3v (suc zero) zero zero zero zero zero , zero ⟩ p₀ p₀)
  where
  p₀ : T6Lattice
  p₀ = zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []
  contra : (suc zero) ≡ zero → ⊥
  contra ()
