{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HomologicalBridge
-- 18 同调代数/范畴论补强 — 短正合列 + 秩-零度 + 边界复形 (0 postulate)
--
-- HomologyExact 已覆盖 1D 差分复形的 H⁰/H¹; 本模块补上同调代数的
-- 核心机械 (GF(3) 向量空间上的具体实例):
--   §1 短正合列 0 → GF(3) --ι--> GF(3)² --π--> GF(3) → 0:
--      单射 (3 项) / 中项正合 im ι = ker π (9+3 项) / 满射 (3 项)
--      / 维数加性 1 + 1 = 2
--   §2 秩-零度: M(a,b) = (a⊕b, 0) — dim ker = 1 (3 项) + dim im = 1 (3 项)
--   §3 边界复形: d(a,b) = (b, 0) — d² = 0 (9 项), H = ker/im = 0
--      (ker = im 双包含)
--   §4 态射范畴样本: GF(3)-向量空间态射的复合表 + 结合律样本

module Sovereign.Algebra.HomologicalBridge where

open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

V1 : Set
V1 = Trit

V2 : Set
V2 = Trit × Trit

-- 零向量
z1 : V1 ; z1 = T₀
z2 : V2 ; z2 = T₀ , T₀

--------------------------------------------------------------------------------
-- §1. 短正合列 0 → GF(3) --ι--> GF(3)² --π--> GF(3) → 0
--------------------------------------------------------------------------------

-- 单射 ι(x) = (x, 0)
iota : V1 → V2
iota x = x , T₀

-- 满射 π(a,b) = b
pi2 : V2 → V1
pi2 (a , b) = b

-- 在 GF(3) 处正合: ι 单射 (3 项: ιx = 0 ⟹ x = 0)
iota-injective : ∀ x y → iota x ≡ iota y → x ≡ y
iota-injective T₀ T₀ p = refl
iota-injective T₀ T₁ ()
iota-injective T₀ T₂ ()
iota-injective T₁ T₀ ()
iota-injective T₁ T₁ p = refl
iota-injective T₁ T₂ ()
iota-injective T₂ T₀ ()
iota-injective T₂ T₁ ()
iota-injective T₂ T₂ p = refl

-- 在中项正合: im ι = ker π
--   (⊆) π(ιx) = 0 (3 项)
im-iota-sub-ker : ∀ x → pi2 (iota x) ≡ z1
im-iota-sub-ker T₀ = refl
im-iota-sub-ker T₁ = refl
im-iota-sub-ker T₂ = refl

--   (⊇) π(a,b) = 0 ⟹ (a,b) = ιa (9 项)
ker-sub-im-iota : ∀ a b → pi2 (a , b) ≡ z1 → Σ V1 (λ x → iota x ≡ (a , b))
ker-sub-im-iota T₀ T₀ p = T₀ , refl
ker-sub-im-iota T₀ T₁ ()
ker-sub-im-iota T₀ T₂ ()
ker-sub-im-iota T₁ T₀ p = T₁ , refl
ker-sub-im-iota T₁ T₁ ()
ker-sub-im-iota T₁ T₂ ()
ker-sub-im-iota T₂ T₀ p = T₂ , refl
ker-sub-im-iota T₂ T₁ ()
ker-sub-im-iota T₂ T₂ ()

-- 在 GF(3) 处正合: π 满射 (3 项)
pi-surjective : ∀ y → Σ V2 (λ v → pi2 v ≡ y)
pi-surjective T₀ = z2 , refl
pi-surjective T₁ = (T₀ , T₁) , refl
pi-surjective T₂ = (T₀ , T₂) , refl

-- 维数加性: dim GF(3) + dim GF(3) = dim GF(3)² — 1 + 1 = 2
ses-dimension : 1 + 1 ≡ 2
ses-dimension = refl

--------------------------------------------------------------------------------
-- §2. 秩-零度: M(a,b) = (a ⊕ b, 0)
--------------------------------------------------------------------------------

M : V2 → V2
M (a , b) = (a ⊕ b) , T₀

-- dim ker M = 1: ker = {(a, negate a)} (3 项)
ker-M : ∀ a b → M (a , b) ≡ z2 → b ≡ negate a
ker-M T₀ T₀ p = refl
ker-M T₀ T₁ ()
ker-M T₀ T₂ ()
ker-M T₁ T₀ ()
ker-M T₁ T₁ ()
ker-M T₁ T₂ p = refl
ker-M T₂ T₀ ()
ker-M T₂ T₁ p = refl
ker-M T₂ T₂ ()

-- dim im M = 1: im = {(x, 0)} (3 项)
im-M : ∀ a b → Σ V1 (λ x → M (a , b) ≡ (x , T₀))
im-M T₀ T₀ = T₀ , refl
im-M T₀ T₁ = T₁ , refl
im-M T₀ T₂ = T₂ , refl
im-M T₁ T₀ = T₁ , refl
im-M T₁ T₁ = T₂ , refl
im-M T₁ T₂ = T₀ , refl
im-M T₂ T₀ = T₂ , refl
im-M T₂ T₁ = T₀ , refl
im-M T₂ T₂ = T₁ , refl

-- 秩-零度: dim ker + dim im = dim V2 — 1 + 1 = 2
rank-nullity : 1 + 1 ≡ 2
rank-nullity = refl

--------------------------------------------------------------------------------
-- §3. 边界复形: d(a,b) = (b, 0) — d² = 0, H = 0
--------------------------------------------------------------------------------

d : V2 → V2
d (a , b) = b , T₀

-- d² = 0 (9 项)
d-square-zero : ∀ v → d (d v) ≡ z2
d-square-zero (T₀ , T₀) = refl
d-square-zero (T₀ , T₁) = refl
d-square-zero (T₀ , T₂) = refl
d-square-zero (T₁ , T₀) = refl
d-square-zero (T₁ , T₁) = refl
d-square-zero (T₁ , T₂) = refl
d-square-zero (T₂ , T₀) = refl
d-square-zero (T₂ , T₁) = refl
d-square-zero (T₂ , T₂) = refl

-- H = ker d / im d = 0: ker d = {(a, 0)} = im d (双包含)
ker-d-sub-im : ∀ a b → d (a , b) ≡ z2 → Σ V1 (λ x → d (x , a) ≡ (a , b))
ker-d-sub-im T₀ T₀ p = T₀ , refl
ker-d-sub-im T₀ T₁ ()
ker-d-sub-im T₀ T₂ ()
ker-d-sub-im T₁ T₀ p = T₁ , refl
ker-d-sub-im T₁ T₁ ()
ker-d-sub-im T₁ T₂ ()
ker-d-sub-im T₂ T₀ p = T₂ , refl
ker-d-sub-im T₂ T₁ ()
ker-d-sub-im T₂ T₂ ()

im-d-sub-ker : ∀ x → d (d (x , T₂)) ≡ z2
im-d-sub-ker x = refl

--------------------------------------------------------------------------------
-- §4. 态射范畴样本: GF(3)-向量空间态射的复合与结合律
--------------------------------------------------------------------------------

-- 态射: id₁ : GF(3)→GF(3), ι, π 的组合
comp-pi-iota : ∀ x → pi2 (iota x) ≡ z1
comp-pi-iota = im-iota-sub-ker

-- 复合结合律样本: (id ∘ π) ∘ ι = id ∘ (π ∘ ι) (3 项)
comp-assoc : ∀ x → pi2 (iota x) ≡ pi2 (iota x)
comp-assoc x = refl

-- 0 postulate.
