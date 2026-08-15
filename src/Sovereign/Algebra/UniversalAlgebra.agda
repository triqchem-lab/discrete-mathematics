{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.UniversalAlgebra
-- 08 一般代数系统 — 代数结构层级 + 实例 + 同态 + 分类 (0 postulate)
--
-- 泛代数的离散落位: 结构记录层级 (半群/幺半群/群/Abel 群/环/域)
-- 在律算合一三大载体 (GF(3) / Z/12Z / GF(9)) 上的实例,
-- 全称同态定理 (保幺元/保持求值) 与域分类 (零因子 ⟹ 非域)。
--
-- 结构: §1 结构记录层级; §2 三大载体实例; §3 同态定理;
--   §4 分类: IsField + 零因子否定定理 + GF(3) 是域 / Z/12Z 非域

module Sovereign.Algebra.UniversalAlgebra where

open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
   ⊕-comm; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ; ⊕-inverse;
   ⊗-comm; ⊗-assoc; ⊗-identityˡ; ⊗-identityʳ;
   ⊗-distribˡ-⊕; ⊗-distribʳ-⊕; ⊗-zeroʳ; negate²)
open import Sovereign.Algebra.Duodecimal using
  (Duodec; d0; d2; d6; _+12_; _*12_; neg12;
   +12-assoc; +12-comm; +12-identityˡ; +12-identityʳ; +12-inverse;
   zero-divisor-2×6)
open import Sovereign.Algebra.GF9 using
  (GF9; _+gf9_; _*gf9_; gf9-one;
   +gf9-assoc; +gf9-comm; +gf9-identityˡ; +gf9-identityʳ; +gf9-inverse;
   *gf9-comm; *gf9-identityˡ; *gf9-identityʳ; *gf9-distribˡ-+gf9)

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

--------------------------------------------------------------------------------
-- §1. 结构记录层级 (08A 代数结构)
--------------------------------------------------------------------------------

record Semigroup (A : Set) : Set₁ where
  infixl 20 _·_
  field
    _·_   : A → A → A
    assoc : ∀ x y z → (x · y) · z ≡ x · (y · z)

record Monoid (A : Set) : Set₁ where
  infixl 20 _·_
  field
    _·_        : A → A → A
    e          : A
    identityˡ  : ∀ x → e · x ≡ x
    identityʳ  : ∀ x → x · e ≡ x
    assoc      : ∀ x y z → (x · y) · z ≡ x · (y · z)

record Group (A : Set) : Set₁ where
  infixl 20 _·_
  field
    _·_       : A → A → A
    e         : A
    inv       : A → A
    identityˡ : ∀ x → e · x ≡ x
    identityʳ : ∀ x → x · e ≡ x
    inverseˡ  : ∀ x → inv x · x ≡ e
    inverseʳ  : ∀ x → x · inv x ≡ e
    assoc     : ∀ x y z → (x · y) · z ≡ x · (y · z)

record AbelianGroup (A : Set) : Set₁ where
  field
    group : Group A
    comm  : ∀ x y → Group._·_ group x y ≡ Group._·_ group y x

record Ring (A : Set) : Set₁ where
  infixl 20 _+_ ; infixl 25 _*_
  field
    _+_ _*_   : A → A → A
    e         : A
    neg       : A → A
    add-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    add-comm  : ∀ x y → x + y ≡ y + x
    add-idˡ   : ∀ x → e + x ≡ x
    add-idʳ   : ∀ x → x + e ≡ x
    add-invˡ  : ∀ x → neg x + x ≡ e
    add-invʳ  : ∀ x → x + neg x ≡ e
    mul-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    mul-one   : A
    mul-idˡ   : ∀ x → mul-one * x ≡ x
    mul-idʳ   : ∀ x → x * mul-one ≡ x
    distribˡ  : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    distribʳ  : ∀ x y z → (y + z) * x ≡ (y * x) + (z * x)
    zeroʳ     : ∀ x → x * e ≡ e

record IsField (A : Set) : Set₁ where
  infixl 20 _+_ ; infixl 25 _*_
  field
    _+_ _*_     : A → A → A
    z o         : A
    +-assoc     : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-identity  : ∀ x → x + z ≡ x
    *-assoc     : ∀ x y z → (x * y) * z ≡ x * (y * z)
    *-idˡ       : ∀ x → o * x ≡ x
    *-idʳ       : ∀ x → x * o ≡ x
    *-zero      : ∀ x → x * z ≡ z
    inv         : ∀ x → x ≢ z → Σ A (λ y → (x * y ≡ o) × (y * x ≡ o))

--------------------------------------------------------------------------------
-- §2. 三大载体实例
--------------------------------------------------------------------------------

-- GF(3) 加法群 (AbelianGroup Trit)
trit-add : AbelianGroup Trit
trit-add = record
  { group = record
    { _·_ = _⊕_; e = T₀; inv = negate
    ; identityˡ = ⊕-identityˡ; identityʳ = ⊕-identityʳ
    ; inverseˡ  = λ x → trans (⊕-comm (negate x) x) (⊕-inverse x)
    ; inverseʳ  = ⊕-inverse
    ; assoc = ⊕-assoc }
  ; comm = ⊕-comm }

-- GF(3) 乘法幺半群 (Monoid Trit)
trit-mul : Monoid Trit
trit-mul = record
  { _·_ = _⊗_; e = T₁
  ; identityˡ = ⊗-identityˡ; identityʳ = ⊗-identityʳ
  ; assoc = ⊗-assoc }

-- GF(3) 环 (Ring Trit)
trit-ring : Ring Trit
trit-ring = record
  { _+_ = _⊕_; _*_ = _⊗_; e = T₀; neg = negate
  ; add-assoc = ⊕-assoc; add-comm = ⊕-comm
  ; add-idˡ = ⊕-identityˡ; add-idʳ = ⊕-identityʳ
  ; add-invˡ = λ x → trans (⊕-comm (negate x) x) (⊕-inverse x)
  ; add-invʳ = ⊕-inverse
  ; mul-assoc = ⊗-assoc; mul-one = T₁
  ; mul-idˡ = ⊗-identityˡ; mul-idʳ = ⊗-identityʳ
  ; distribˡ = ⊗-distribˡ-⊕; distribʳ = λ x y z → ⊗-distribʳ-⊕ y z x
  ; zeroʳ = ⊗-zeroʳ }

-- Z/12Z 加法群 (AbelianGroup Duodec)
duodec-add : AbelianGroup Duodec
duodec-add = record
  { group = record
    { _·_ = _+12_; e = d0; inv = neg12
    ; identityˡ = +12-identityˡ; identityʳ = +12-identityʳ
    ; inverseˡ  = λ x → trans (+12-comm (neg12 x) x) (+12-inverse x)
    ; inverseʳ  = +12-inverse
    ; assoc = +12-assoc }
  ; comm = +12-comm }

-- GF(9) 加法群 (AbelianGroup GF9)
gf9-add : AbelianGroup GF9
gf9-add = record
  { group = record
    { _·_ = _+gf9_; e = (T₀ , T₀)
    ; inv = λ x → negate (proj₁ x) , negate (proj₂ x)
    ; identityˡ = +gf9-identityˡ; identityʳ = +gf9-identityʳ
    ; inverseˡ  = λ x → trans (+gf9-comm (negate (proj₁ x) , negate (proj₂ x)) x) (+gf9-inverse x)
    ; inverseʳ  = +gf9-inverse
    ; assoc = +gf9-assoc }
  ; comm = +gf9-comm }
  where open import Data.Product using (proj₁; proj₂)

-- GF(9) 乘法交换幺半群 (Monoid GF9 — 结合律 *gf9-assoc 留待, 见注)
-- GF(9) 乘法交换性 + 单位 (Monoid 的 assoc 层留待 *gf9-assoc 符号证 —
-- GF9AlgebraicChain l4 已以 *s 星乘载体完成同级结构; 不以 postulate 驻留)
gf9-mul-comm : ∀ x y → x *gf9 y ≡ y *gf9 x
gf9-mul-comm = *gf9-comm

gf9-mul-identityˡ : ∀ x → gf9-one *gf9 x ≡ x
gf9-mul-identityˡ = *gf9-identityˡ

gf9-mul-identityʳ : ∀ x → x *gf9 gf9-one ≡ x
gf9-mul-identityʳ = *gf9-identityʳ

-- GF(9) 乘法对加法的右分配 (由左分配 + 交换导出)
gf9-distribʳ : ∀ x y z → (y +gf9 z) *gf9 x ≡ (y *gf9 x) +gf9 (z *gf9 x)
gf9-distribʳ x y z = begin
  (y +gf9 z) *gf9 x
    ≡⟨ *gf9-comm (y +gf9 z) x ⟩
  x *gf9 (y +gf9 z)
    ≡⟨ *gf9-distribˡ-+gf9 x y z ⟩
  (x *gf9 y) +gf9 (x *gf9 z)
    ≡⟨ cong₂ _+gf9_ (*gf9-comm x y) (*gf9-comm x z) ⟩
  (y *gf9 x) +gf9 (z *gf9 x) ∎

--------------------------------------------------------------------------------
-- §3. 同态定理 (全称)
--------------------------------------------------------------------------------

-- 群同态保幺元: h(e) = e (从同态 + 群公理导出)
hom-preserves-zero : ∀ (h : Trit → Trit)
  → (∀ a b → h (a ⊕ b) ≡ h a ⊕ h b) → h T₀ ≡ T₀
hom-preserves-zero h hom = begin
  h T₀
    ≡⟨ sym (⊕-identityʳ (h T₀)) ⟩
  h T₀ ⊕ T₀
    ≡⟨ cong (h T₀ ⊕_) (sym (⊕-inverse (h T₀))) ⟩
  h T₀ ⊕ (h T₀ ⊕ negate (h T₀))
    ≡⟨ sym (⊕-assoc (h T₀) (h T₀) (negate (h T₀))) ⟩
  (h T₀ ⊕ h T₀) ⊕ negate (h T₀)
    ≡⟨ cong (_⊕ negate (h T₀)) (sym (hom T₀ T₀)) ⟩
  h (T₀ ⊕ T₀) ⊕ negate (h T₀)
    ≡⟨ cong (_⊕ negate (h T₀)) (cong h (⊕-identityˡ T₀)) ⟩
  h T₀ ⊕ negate (h T₀)
    ≡⟨ ⊕-inverse (h T₀) ⟩
  T₀ ∎

-- 深度 ≤ 2 的 ⊕-项 (变量 x, y, 常数 T₀)
data Term2 : Set where
  VX VY CZ : Term2
  ADD : Term2 → Term2 → Term2

eval : Term2 → Trit → Trit → Trit
eval VX x y = x
eval VY x y = y
eval CZ x y = T₀
eval (ADD t u) x y = eval t x y ⊕ eval u x y

-- 同态保持求值 (项代数语义): h(eval t x y) = eval t (h x) (h y)
hom-preserves-eval : ∀ (h : Trit → Trit)
  → (∀ a b → h (a ⊕ b) ≡ h a ⊕ h b)
  → ∀ t x y → h (eval t x y) ≡ eval t (h x) (h y)
hom-preserves-eval h hom VX x y = refl
hom-preserves-eval h hom VY x y = refl
hom-preserves-eval h hom CZ x y = hom-preserves-zero h hom
hom-preserves-eval h hom (ADD t u) x y =
  trans (hom (eval t x y) (eval u x y))
        (cong₂ _⊕_ (hom-preserves-eval h hom t x y)
                   (hom-preserves-eval h hom u x y))

-- negate 是 ⊕-自同构 (9 项) + 对合 (negate²) — 泛代数的自同构实例
negate-add-hom : ∀ x y → negate (x ⊕ y) ≡ negate x ⊕ negate y
negate-add-hom T₀ T₀ = refl
negate-add-hom T₀ T₁ = refl
negate-add-hom T₀ T₂ = refl
negate-add-hom T₁ T₀ = refl
negate-add-hom T₁ T₁ = refl
negate-add-hom T₁ T₂ = refl
negate-add-hom T₂ T₀ = refl
negate-add-hom T₂ T₁ = refl
negate-add-hom T₂ T₂ = refl

negate-is-automorphism : ∀ x y → negate (x ⊕ y) ≡ negate x ⊕ negate y
negate-is-automorphism = negate-add-hom

--------------------------------------------------------------------------------
-- §4. 分类 (08A): 零因子 ⟹ 非域 (全称) + GF(3) 是域 / Z/12Z 非域
--------------------------------------------------------------------------------

-- 全称定理 (具体零参数化版): 域中无零因子 —
--   若 z F ≡ z₀ 且 a·b ≡ z₀, 则 a ≢ z₀ 与 b ≢ z₀ 不可同时成立
zero-divisor-not-field : ∀ {A : Set} (F : IsField A) → ∀ z₀ a b
  → IsField.z F ≡ z₀ → IsField._*_ F a b ≡ z₀
  → a ≢ z₀ → b ≢ z₀ → ⊥
zero-divisor-not-field F z₀ a b zF zab na nb = nb (begin
  b
    ≡⟨ sym (*-idˡ b) ⟩
  o * b
    ≡⟨ cong (_* b) (sym ya-o) ⟩
  (y * a) * b
    ≡⟨ *-assoc y a b ⟩
  y * (a * b)
    ≡⟨ cong (y *_) zab' ⟩
  y * z
    ≡⟨ *-zero y ⟩
  z
    ≡⟨ zF ⟩
  z₀ ∎)
  where
  open IsField F
  na' : a ≢ z
  na' = λ eq → na (trans eq zF)
  zab' : a * b ≡ z
  zab' = trans zab (sym zF)
  y = proj₁ (inv a na')
  ya-o = proj₂ (proj₂ (inv a na'))

-- GF(3) 是域: 非零元的逆 (2 项)
trit-field : IsField Trit
trit-field = record
  { _+_ = _⊕_; _*_ = _⊗_; z = T₀; o = T₁
  ; +-assoc = ⊕-assoc; +-identity = ⊕-identityʳ
  ; *-assoc = ⊗-assoc; *-idˡ = ⊗-identityˡ; *-idʳ = ⊗-identityʳ
  ; *-zero = ⊗-zeroʳ
  ; inv = trit-inv }
  where
  trit-inv : ∀ x → x ≢ T₀ → Σ Trit (λ y → (x ⊗ y ≡ T₁) × (y ⊗ x ≡ T₁))
  trit-inv T₀ nz = ⊥-elim (nz refl)
  trit-inv T₁ nz = T₁ , refl , refl
  trit-inv T₂ nz = T₂ , refl , refl

-- Z/12Z 非域: 2 × 6 = 0 且 2, 6 ≢ 0 (零因子见证, 引用 Duodecial)
-- 精确陈述: 不存在以 *12 为乘法、以 d0 为零元的 Duodec 域结构
duodec-not-field :
  ¬ (Σ (IsField Duodec) (λ F → (IsField.z F ≡ d0) ×
     (∀ a b → IsField._*_ F a b ≡ a *12 b)))
duodec-not-field (F , zF , Fmul) =
  zero-divisor-not-field F d0 d2 d6 zF
    (trans (Fmul d2 d6) zero-divisor-2×6) (λ ()) (λ ())

-- 0 postulate.
