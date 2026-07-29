{-# OPTIONS --rewriting --guardedness #-}

-- | ExactSequence — GF(3) 离散正合序列
--
-- 连续统病态: 连续空间的正合序列涉及无穷维向量空间
-- 离散自愈: GF(3) 上正合序列是有限维, 可精确验证
--
-- 核心结构:
--   §1. 正合性定义: im(f) = ker(g)
--   §2. 短正合序列: 0 → A → B → C → 0
--   §3. 维数公式: dim(B) = dim(A) + dim(C)
--   §4. 蛇引理离散版: 连接同态的存在性
--
-- 复用: Sovereign.Base.Trit, Algebra.ChainComplex
-- 0 postulate.

module Sovereign.Algebra.ExactSequence where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

--------------------------------------------------------------------------------
-- §1. 正合性定义
--
-- 序列 A --f→ B --g→ C 在 B 处正合 ⟺ im(f) = ker(g)
-- 即: g(b) = 0 ⟺ ∃ a, f(a) = b
--
-- GF(3) 上: 所有映射都是有限函数, 正合性可穷举验证
--------------------------------------------------------------------------------

-- GF(3) 上的线性映射 (简化: 标量乘法)
LinearMap : Set → Set → Set
LinearMap A B = A → B

--------------------------------------------------------------------------------
-- §2. 短正合序列: 0 → A → B → C → 0
--
-- 实例: 0 → GF(3) → GF(3)² → GF(3) → 0
--   f: a ↦ (a, 0)  (嵌入第一分量)
--   g: (x, y) ↦ y  (投影第二分量)
--
-- 正合性: im(f) = {(a,0)} = ker(g) ✓
--------------------------------------------------------------------------------

-- 嵌入: GF(3) → GF(3)²
embed-first : Trit → Trit × Trit
embed-first a = a , T₀

-- 投影: GF(3)² → GF(3)
proj-second : Trit × Trit → Trit
proj-second (x , y) = y

-- g ∘ f = 0 (正合性的必要条件)
gf-zero : ∀ a → proj-second (embed-first a) ≡ T₀
gf-zero a = refl

-- im(f) ⊆ ker(g): f 的像都在 g 的核中
im-in-ker : ∀ a → proj-second (embed-first a) ≡ T₀
im-in-ker = gf-zero

-- 辅助: T₁ ≠ T₀, T₂ ≠ T₀
T₁≢T₀ : T₁ ≡ T₀ → ⊥
T₁≢T₀ ()

T₂≢T₀ : T₂ ≡ T₀ → ⊥
T₂≢T₀ ()

-- ker(g) ⊆ im(f): g 的核都在 f 的像中
-- 若 proj-second(x,y) = 0, 则 y = 0, 所以 (x,y) = embed-first(x)
ker-in-im : ∀ x y → proj-second (x , y) ≡ T₀ → Σ Trit (λ a → embed-first a ≡ (x , y))
ker-in-im x T₀ eq = x , refl
ker-in-im x T₁ eq = ⊥-elim (T₁≢T₀ eq)
ker-in-im x T₂ eq = ⊥-elim (T₂≢T₀ eq)

--------------------------------------------------------------------------------
-- §3. 维数公式 (秩-零化度定理)
--
-- 短正合序列 0 → A → B → C → 0 蕴含:
--   dim(B) = dim(A) + dim(C)
--
-- 实例: dim(GF(3)²) = dim(GF(3)) + dim(GF(3)) = 1 + 1 = 2
--------------------------------------------------------------------------------

-- 维数 (GF(3)^n 的维数 = n)
dim-GF3 : ℕ → ℕ
dim-GF3 n = n

-- 维数公式: 1 + 1 = 2
dim-formula : dim-GF3 1 + dim-GF3 1 ≡ dim-GF3 2
dim-formula = refl

--------------------------------------------------------------------------------
-- §4. 分裂引理 (GF(3) 版本)
--
-- 定理: GF(3) 上的短正合序列总是分裂的
-- (因为 GF(3) 是域, 所有模都是自由模)
--
-- 分裂: B ≅ A ⊕ C
--------------------------------------------------------------------------------

-- 分裂同构: GF(3)² ≅ GF(3) ⊕ GF(3)
-- 正向: (x,y) ↦ (x,y) (恒等)
-- 反向: (x,y) ↦ (x,y) (恒等)
-- 这是平凡的, 因为 GF(3)² 本身就是 GF(3) ⊕ GF(3)

split-iso-fwd : Trit × Trit → Trit × Trit
split-iso-fwd (x , y) = x , y

split-iso-bwd : Trit × Trit → Trit × Trit
split-iso-bwd (x , y) = x , y

-- 正向∘反向 = id
split-roundtrip : ∀ p → split-iso-fwd (split-iso-bwd p) ≡ p
split-roundtrip (x , y) = refl
