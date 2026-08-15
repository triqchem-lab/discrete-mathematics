{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.A4Representations
-- A₄ 群的不可约表示理论 (补强版, 2026-08, 0 postulate)
--
-- 核心结果:
--   1. A₄ 有恰好 4 个共轭类: C₁(1), C₂(4), C₃(4), C₄(3)
--   2. 四个特征标 {3, 1, 1′, 1″} 满足完整第一正交关系 (4×4 全 16 项):
--      ⟨χᵢ, χⱼ⟩ = Σ_C |C|·χᵢ(C)·conj(χⱼ(C)) = 12·δᵢⱼ — char-orthogonality
--   3. 维数平方和: 3² + 1² + 1² + 1² = 12 = |A₄|
--   4. V₃ = 置换表示去掉全对称分量: 三个基向量 sum=0 (basisSumZero),
--      置换作用保持坐标和 (sumZero-invariant, 13 case 显式),
--      特征标分解 χ_perm = χ₁ + χ₃ (perm-char-decomp)
--   5. V₁, V₁′, V₁″ = 通过 Abel 化 A₄/V₄ ≅ C₃ 拉回的三个特征标,
--      全部为群同态 (multiplicative, abelianize-hom 144 case) 且两两相异
--   6. 三代费米子 = 三个一维特征标 (singlets) + 三维标准表示 (triplet)
--
-- 诚实边界:
--   (a) 经典定理 ⟨χ,χ⟩=|G| ⟺ 不可约 (第一正交关系 → 不可约) 是有限群
--       特征标理论的引用结果, 不在本库内落链; 本模块验证的是该判据的
--       计算侧: 全部四个 ⟨χᵢ,χᵢ⟩ ≡ 12 (irrep-norm-criterion)。
--   (b) "三代费米子是必然的"的物理对应 (A₄ 味对称 ↔ Altarelli-Feruglio)
--       是框架层解读, 本模块只做代数层: 三个一维特征标存在、相异、完备。
--
-- 方法: 编码查表 (encodeA4 → ℕ) + 构造子实例化, 无 with, 无 postulate。
--   注意: 本模块修正了旧版共轭类分派错误 (C2 = 编码 {3,6,9,12}, C3 = {2,7,8,13},
--   与 V₄ 陪集一致 — 旧版混类使 abelianize 不成为同态, 由乘性表 144 例暴露)。

module Sovereign.Structology.A4Representations where

infixl 6 _·₃_

open import Data.Nat using (ℕ; zero; suc)
  renaming (_+_ to _+N_; _*_ to _*N_)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.Integer.Properties using (+-assoc; +-comm)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Structology.A4Group
  using (A4; Id; Rot; Flip; perm; _⊗_; _∘ₚ_; perm-hom)
open import Sovereign.RootMath.Eisenstein
  using (Eisenstein; eis; 0ᵉ; 1ᵉ; ωᵉ; ω²ᵉ; -1ᵉ; 3ᵉ; _+ᵉ_; _*ᵉ_; conjᵉ; conjᵉ-mul)

--------------------------------------------------------------------------------
-- 1. A₄ 元素编码 (perm → ℕ 查表)
--------------------------------------------------------------------------------

encodeA4 : A4 → ℕ
encodeA4 g = toℕ (perm g zero) *N 4 +N toℕ (perm g (suc zero))

--------------------------------------------------------------------------------
-- 2. 共轭类
--------------------------------------------------------------------------------

data ConjugacyClass : Set where
  C1 : ConjugacyClass  -- {Id} (size 1)
  C2 : ConjugacyClass  -- 顺时针 3-cycles (size 4)
  C3 : ConjugacyClass  -- 逆时针 3-cycles (size 4)
  C4 : ConjugacyClass  -- 双对换 (size 3)

classSize : ConjugacyClass → ℕ
classSize C1 = 1
classSize C2 = 4
classSize C3 = 4
classSize C4 = 3

classSizeSum : classSize C1 +N classSize C2 +N classSize C3 +N classSize C4 ≡ 12
classSizeSum = refl

lookup-class : ℕ → ConjugacyClass
lookup-class 1  = C1   -- Id
lookup-class 2  = C3   -- Rot zero zero        : (1 2 3) — ω² 类
lookup-class 3  = C2   -- Rot zero (suc zero)  : (1 3 2) — ω 类
lookup-class 4  = C4   -- Flip zero
lookup-class 6  = C2   -- Rot (suc (suc (suc zero))) zero : (0 1 2) — ω 类
lookup-class 7  = C3   -- Rot (suc (suc zero)) zero       : (0 1 3) — ω² 类
lookup-class 8  = C3   -- Rot (suc (suc (suc zero))) (suc zero) : (0 2 1) — ω² 类
lookup-class 9  = C2   -- Rot (suc zero) zero  : (0 2 3) — ω 类
lookup-class 11 = C4   -- Flip (suc zero)
lookup-class 12 = C2   -- Rot (suc (suc zero)) (suc zero) : (0 3 1) — ω 类
lookup-class 13 = C3   -- Rot (suc zero) (suc zero) : (0 3 2) — ω² 类
lookup-class 14 = C4   -- Flip (suc (suc zero))
lookup-class _  = C1

classify : A4 → ConjugacyClass
classify g = lookup-class (encodeA4 g)

--------------------------------------------------------------------------------
-- 3. 不可约表示类型与特征标表
--------------------------------------------------------------------------------

data A4Irrep : Set where
  V3   : A4Irrep  -- 三维标准表示
  V1   : A4Irrep  -- 一维平凡表示
  V1'  : A4Irrep  -- 一维: 3-cycle → ω
  V1'' : A4Irrep  -- 一维: 3-cycle → ω²

dim : A4Irrep → ℕ
dim V3   = 3
dim V1   = 1
dim V1'  = 1
dim V1'' = 1

dimSqSum : dim V3 *N dim V3 +N dim V1 *N dim V1 +N dim V1' *N dim V1' +N dim V1'' *N dim V1'' ≡ 12
dimSqSum = refl

-- 特征标表 (共轭类上)
charAt : A4Irrep → ConjugacyClass → Eisenstein
-- V3: χ₃(C1)=3, χ₃(C2)=0, χ₃(C3)=0, χ₃(C4)=-1
charAt V3 C1 = 3ᵉ
charAt V3 C2 = 0ᵉ
charAt V3 C3 = 0ᵉ
charAt V3 C4 = -1ᵉ
-- V1: 平凡
charAt V1 _  = 1ᵉ
-- V1': χ(C1)=1, χ(C2)=ω, χ(C3)=ω², χ(C4)=1
charAt V1' C1 = 1ᵉ
charAt V1' C2 = ωᵉ
charAt V1' C3 = ω²ᵉ
charAt V1' C4 = 1ᵉ
-- V1'': χ(C1)=1, χ(C2)=ω², χ(C3)=ω, χ(C4)=1
charAt V1'' C1 = 1ᵉ
charAt V1'' C2 = ω²ᵉ
charAt V1'' C3 = ωᵉ
charAt V1'' C4 = 1ᵉ

character : A4Irrep → A4 → Eisenstein
character irr g = charAt irr (classify g)

--------------------------------------------------------------------------------
-- 4. 第一正交关系 (完整 4×4, 16 项)
--    ⟨f, g⟩ = Σ_C |C|·f(C)·conj(g(C)) — 有限 Eisenstein 计算
--------------------------------------------------------------------------------

eis12 : Eisenstein
eis12 = eis (+ 12) (+ 0)

classSizeᵉ : ConjugacyClass → Eisenstein
classSizeᵉ c = eis (+ (classSize c)) (+ 0)

inner : (ConjugacyClass → Eisenstein) → (ConjugacyClass → Eisenstein) → Eisenstein
inner f g =
  classSizeᵉ C1 *ᵉ (f C1 *ᵉ conjᵉ (g C1))
  +ᵉ (classSizeᵉ C2 *ᵉ (f C2 *ᵉ conjᵉ (g C2))
  +ᵉ (classSizeᵉ C3 *ᵉ (f C3 *ᵉ conjᵉ (g C3))
  +ᵉ (classSizeᵉ C4 *ᵉ (f C4 *ᵉ conjᵉ (g C4)))))

-- Kronecker × 12: δᵢⱼ · |A₄|
kronecker12 : A4Irrep → A4Irrep → Eisenstein
kronecker12 V3 V3     = eis12
kronecker12 V3 _      = 0ᵉ
kronecker12 V1 V3     = 0ᵉ
kronecker12 V1 V1     = eis12
kronecker12 V1 _      = 0ᵉ
kronecker12 V1' V3    = 0ᵉ
kronecker12 V1' V1    = 0ᵉ
kronecker12 V1' V1'   = eis12
kronecker12 V1' _     = 0ᵉ
kronecker12 V1'' V3   = 0ᵉ
kronecker12 V1'' V1   = 0ᵉ
kronecker12 V1'' V1'  = 0ᵉ
kronecker12 V1'' V1'' = eis12

-- 完整第一正交关系: ⟨χᵢ, χⱼ⟩ ≡ 12·δᵢⱼ (16 case refl)
char-orthogonality : ∀ i j → inner (charAt i) (charAt j) ≡ kronecker12 i j
char-orthogonality V3 V3 = refl
char-orthogonality V3 V1 = refl
char-orthogonality V3 V1' = refl
char-orthogonality V3 V1'' = refl
char-orthogonality V1 V3 = refl
char-orthogonality V1 V1 = refl
char-orthogonality V1 V1' = refl
char-orthogonality V1 V1'' = refl
char-orthogonality V1' V3 = refl
char-orthogonality V1' V1 = refl
char-orthogonality V1' V1' = refl
char-orthogonality V1' V1'' = refl
char-orthogonality V1'' V3 = refl
char-orthogonality V1'' V1 = refl
char-orthogonality V1'' V1' = refl
char-orthogonality V1'' V1'' = refl

-- 不可约性判据的计算侧 (经典 ⟨χ,χ⟩=|G| ⟺ 不可约 的等价方向为引用边界):
-- 全部四个特征标自内积 ≡ |A₄| = 12
irrep-norm-criterion : ∀ i → inner (charAt i) (charAt i) ≡ eis12
irrep-norm-criterion V3   = char-orthogonality V3 V3
irrep-norm-criterion V1   = char-orthogonality V1 V1
irrep-norm-criterion V1'  = char-orthogonality V1' V1'
irrep-norm-criterion V1'' = char-orthogonality V1'' V1''

-- 特征标实例
χ₃-values : (character V3 Id ≡ 3ᵉ) × (character V3 (Rot zero zero) ≡ 0ᵉ) × (character V3 (Flip zero) ≡ -1ᵉ)
χ₃-values = refl , refl , refl

χ₁-values : ∀ (g : A4) → character V1 g ≡ 1ᵉ
χ₁-values Id = refl
χ₁-values (Rot _ _) = refl
χ₁-values (Flip _) = refl

χ₁'-on-3cycles : character V1' (Rot zero zero) ≡ ω²ᵉ × character V1' (Rot zero (suc zero)) ≡ ωᵉ
χ₁'-on-3cycles = refl , refl

-- V1'' = conj(V1') — 逐共轭类验证 (无 with, 构造子实例化)
χ₁''-is-conj-χ₁' : ∀ (g : A4) → character V1'' g ≡ conjᵉ (character V1' g)
χ₁''-is-conj-χ₁' g = charAt-conj (classify g)
  where
  charAt-conj : ∀ c → charAt V1'' c ≡ conjᵉ (charAt V1' c)
  charAt-conj C1 = refl
  charAt-conj C2 = refl
  charAt-conj C3 = refl
  charAt-conj C4 = refl

character-at-identity : (character V3 Id ≡ 3ᵉ) × (character V1 Id ≡ 1ᵉ) × (character V1' Id ≡ 1ᵉ) × (character V1'' Id ≡ 1ᵉ)
character-at-identity = refl , refl , refl , refl

-- 四个特征标两两相异 (三代 singlet 的区分性)
chars-distinct :
  (character V1' (Rot zero zero) ≢ character V1 (Rot zero zero)) ×
  (character V1'' (Rot zero zero) ≢ character V1 (Rot zero zero)) ×
  (character V1'' (Rot zero zero) ≢ character V1' (Rot zero zero)) ×
  (character V3 Id ≢ character V1 Id)
chars-distinct = (λ ()) , (λ ()) , (λ ()) , (λ ())

--------------------------------------------------------------------------------
-- 5. V₃ = 置换表示去掉全对称分量 (sum=0 子空间)
--------------------------------------------------------------------------------

V3basis1 : Vec ℤ 4
V3basis1 = (+ 1) ∷ (-[1+ 0 ]) ∷ (+ 0) ∷ (+ 0) ∷ []

V3basis2 : Vec ℤ 4
V3basis2 = (+ 1) ∷ (+ 0) ∷ (-[1+ 0 ]) ∷ (+ 0) ∷ []

V3basis3 : Vec ℤ 4
V3basis3 = (+ 1) ∷ (+ 0) ∷ (+ 0) ∷ (-[1+ 0 ]) ∷ []

sumVec4 : Vec ℤ 4 → ℤ
sumVec4 (a ∷ b ∷ c ∷ d ∷ []) = a + (b + (c + d))

-- 三个基向量坐标和为零 (真命题: sum=0 子空间的显式基)
basisSumZero : (sumVec4 V3basis1 ≡ + 0) × (sumVec4 V3basis2 ≡ + 0) × (sumVec4 V3basis3 ≡ + 0)
basisSumZero = refl , refl , refl

-- A₄ 在 ℤ⁴ 上的置换作用 (坐标置换)
act : A4 → Vec ℤ 4 → Vec ℤ 4
act g v =
  lookup v (perm g zero)
  ∷ lookup v (perm g (suc zero))
  ∷ lookup v (perm g (suc (suc zero)))
  ∷ lookup v (perm g (suc (suc (suc zero))))
  ∷ []

-- 求和重排原语 (ℤ, 右结合嵌套)
swap34 : ∀ a b c d → a + (b + (c + d)) ≡ a + (b + (d + c))
swap34 a b c d = cong (λ t → a + t) (cong (λ t → b + t) (+-comm c d))

swap01 : ∀ a b r → a + (b + r) ≡ b + (a + r)
swap01 a b r = begin
  a + (b + r)
    ≡⟨ sym (+-assoc a b r) ⟩
  (a + b) + r
    ≡⟨ cong (λ t → t + r) (+-comm a b) ⟩
  (b + a) + r
    ≡⟨ +-assoc b a r ⟩
  b + (a + r) ∎

rot3cw : ∀ a b c → b + (c + a) ≡ a + (b + c)
rot3cw a b c = begin
  b + (c + a)
    ≡⟨ sym (+-assoc b c a) ⟩
  (b + c) + a
    ≡⟨ +-comm (b + c) a ⟩
  a + (b + c) ∎

rot3ccw : ∀ a b c → c + (a + b) ≡ a + (b + c)
rot3ccw a b c = begin
  c + (a + b)
    ≡⟨ sym (+-assoc c a b) ⟩
  (c + a) + b
    ≡⟨ cong (λ t → t + b) (+-comm c a) ⟩
  (a + c) + b
    ≡⟨ +-assoc a c b ⟩
  a + (c + b)
    ≡⟨ cong (λ t → a + t) (+-comm c b) ⟩
  a + (b + c) ∎

-- 3-轮换作用下的求和重排 (固定顶点 0/1/2/3 × 方向 cw/ccw)
fix0-cw : ∀ a b c d → a + (c + (d + b)) ≡ a + (b + (c + d))
fix0-cw a b c d = cong (λ t → a + t) (rot3cw b c d)

fix0-ccw : ∀ a b c d → a + (d + (b + c)) ≡ a + (b + (c + d))
fix0-ccw a b c d = cong (λ t → a + t) (rot3ccw b c d)

fix1-cw : ∀ a b c d → c + (b + (d + a)) ≡ a + (b + (c + d))
fix1-cw a b c d = begin
  c + (b + (d + a))
    ≡⟨ cong (λ t → c + t) (rot3cw a b d) ⟩
  c + (a + (b + d))
    ≡⟨ swap01 c a (b + d) ⟩
  a + (c + (b + d))
    ≡⟨ cong (λ t → a + t) (rot3ccw b d c) ⟩
  a + (b + (d + c))
    ≡⟨ cong (λ t → a + t) (cong (λ t → b + t) (+-comm d c)) ⟩
  a + (b + (c + d)) ∎

fix1-ccw : ∀ a b c d → d + (b + (a + c)) ≡ a + (b + (c + d))
fix1-ccw a b c d = begin
  d + (b + (a + c))
    ≡⟨ cong (λ t → d + t) (swap01 b a c) ⟩
  d + (a + (b + c))
    ≡⟨ rot3ccw a (b + c) d ⟩
  a + ((b + c) + d)
    ≡⟨ cong (λ t → a + t) (+-assoc b c d) ⟩
  a + (b + (c + d)) ∎

fix2-cw : ∀ a b c d → b + (d + (c + a)) ≡ a + (b + (c + d))
fix2-cw a b c d = begin
  b + (d + (c + a))
    ≡⟨ cong (λ t → b + t) (cong (λ t → d + t) (+-comm c a)) ⟩
  b + (d + (a + c))
    ≡⟨ cong (λ t → b + t) (rot3ccw a c d) ⟩
  b + (a + (c + d))
    ≡⟨ swap01 b a (c + d) ⟩
  a + (b + (c + d)) ∎

fix2-ccw : ∀ a b c d → d + (a + (c + b)) ≡ a + (b + (c + d))
fix2-ccw a b c d = begin
  d + (a + (c + b))
    ≡⟨ cong (λ t → d + t) (cong (λ t → a + t) (+-comm c b)) ⟩
  d + (a + (b + c))
    ≡⟨ rot3ccw a (b + c) d ⟩
  a + ((b + c) + d)
    ≡⟨ cong (λ t → a + t) (+-assoc b c d) ⟩
  a + (b + (c + d)) ∎

fix3-cw : ∀ a b c d → b + (c + (a + d)) ≡ a + (b + (c + d))
fix3-cw a b c d = begin
  b + (c + (a + d))
    ≡⟨ cong (λ t → b + t) (swap01 c a d) ⟩
  b + (a + (c + d))
    ≡⟨ swap01 b a (c + d) ⟩
  a + (b + (c + d)) ∎

fix3-ccw : ∀ a b c d → c + (a + (b + d)) ≡ a + (b + (c + d))
fix3-ccw a b c d = begin
  c + (a + (b + d))
    ≡⟨ swap01 c a (b + d) ⟩
  a + (c + (b + d))
    ≡⟨ cong (λ t → a + t) (rot3ccw b d c) ⟩
  a + (b + (d + c))
    ≡⟨ cong (λ t → a + t) (cong (λ t → b + t) (+-comm d c)) ⟩
  a + (b + (c + d)) ∎

flip01 : ∀ a b c d → b + (a + (d + c)) ≡ a + (b + (c + d))
flip01 a b c d = begin
  b + (a + (d + c))
    ≡⟨ cong (λ t → b + t) (cong (λ t → a + t) (+-comm d c)) ⟩
  b + (a + (c + d))
    ≡⟨ swap01 b a (c + d) ⟩
  a + (b + (c + d)) ∎

flip02 : ∀ a b c d → c + (d + (a + b)) ≡ a + (b + (c + d))
flip02 a b c d = begin
  c + (d + (a + b))
    ≡⟨ cong (λ t → c + t) (swap01 d a b) ⟩
  c + (a + (d + b))
    ≡⟨ swap01 c a (d + b) ⟩
  a + (c + (d + b))
    ≡⟨ cong (λ t → a + t) (rot3cw b c d) ⟩
  a + (b + (c + d)) ∎

flip03 : ∀ a b c d → d + (c + (b + a)) ≡ a + (b + (c + d))
flip03 a b c d = begin
  d + (c + (b + a))
    ≡⟨ cong (λ t → d + t) (cong (λ t → c + t) (+-comm b a)) ⟩
  d + (c + (a + b))
    ≡⟨ cong (λ t → d + t) (swap01 c a b) ⟩
  d + (a + (c + b))
    ≡⟨ cong (λ t → d + t) (cong (λ t → a + t) (+-comm c b)) ⟩
  d + (a + (b + c))
    ≡⟨ rot3ccw a (b + c) d ⟩
  a + ((b + c) + d)
    ≡⟨ cong (λ t → a + t) (+-assoc b c d) ⟩
  a + (b + (c + d)) ∎

-- 置换作用保持坐标和 (12 个非平凡元素显式, 无 with)
sumZero-invariant : ∀ g v → sumVec4 (act g v) ≡ sumVec4 v
sumZero-invariant Id (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = refl
sumZero-invariant (Rot zero zero) (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = fix0-cw v0 v1 v2 v3
sumZero-invariant (Rot zero (suc zero)) (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = fix0-ccw v0 v1 v2 v3
sumZero-invariant (Rot (suc zero) zero) (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = fix1-cw v0 v1 v2 v3
sumZero-invariant (Rot (suc zero) (suc zero)) (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = fix1-ccw v0 v1 v2 v3
sumZero-invariant (Rot (suc (suc zero)) zero) (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = fix2-cw v0 v1 v2 v3
sumZero-invariant (Rot (suc (suc zero)) (suc zero)) (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = fix2-ccw v0 v1 v2 v3
sumZero-invariant (Rot (suc (suc (suc zero))) zero) (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = fix3-cw v0 v1 v2 v3
sumZero-invariant (Rot (suc (suc (suc zero))) (suc zero)) (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = fix3-ccw v0 v1 v2 v3
sumZero-invariant (Flip zero) (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = flip01 v0 v1 v2 v3
sumZero-invariant (Flip (suc zero)) (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = flip02 v0 v1 v2 v3
sumZero-invariant (Flip (suc (suc zero))) (v0 ∷ v1 ∷ v2 ∷ v3 ∷ []) = flip03 v0 v1 v2 v3

-- sum=0 子空间在 A₄ 作用下不变
act-preserves-L : ∀ g v → sumVec4 v ≡ + 0 → sumVec4 (act g v) ≡ + 0
act-preserves-L g v sv0 = trans (sumZero-invariant g v) sv0

--------------------------------------------------------------------------------
-- 6. 置换特征标分解: χ_perm = χ₁ + χ₃ (三维 = 置换表示去掉全对称分量)
--------------------------------------------------------------------------------

fixCountC : ConjugacyClass → ℕ
fixCountC C1 = 4
fixCountC C2 = 1
fixCountC C3 = 1
fixCountC C4 = 0

fixChar : A4 → Eisenstein
fixChar g = eis (+ (fixCountC (classify g))) (+ 0)

perm-char-decomp-c : ∀ c →
  eis (+ (fixCountC c)) (+ 0) ≡ charAt V1 c +ᵉ charAt V3 c
perm-char-decomp-c C1 = refl
perm-char-decomp-c C2 = refl
perm-char-decomp-c C3 = refl
perm-char-decomp-c C4 = refl

perm-char-decomp : ∀ g → fixChar g ≡ character V1 g +ᵉ character V3 g
perm-char-decomp g = perm-char-decomp-c (classify g)

--------------------------------------------------------------------------------
-- 7. Abel 化: A₄ → C₃ (三个一维特征标的拉回来源)
--------------------------------------------------------------------------------

data C3Group : Set where
  c3-1  : C3Group
  c3-a  : C3Group
  c3-a² : C3Group

_·₃_ : C3Group → C3Group → C3Group
c3-1 ·₃ y = y
c3-a ·₃ c3-1 = c3-a
c3-a ·₃ c3-a = c3-a²
c3-a ·₃ c3-a² = c3-1
c3-a² ·₃ c3-1 = c3-a²
c3-a² ·₃ c3-a = c3-1
c3-a² ·₃ c3-a² = c3-a

lookup-abel : ConjugacyClass → C3Group
lookup-abel C1 = c3-1
lookup-abel C2 = c3-a
lookup-abel C3 = c3-a²
lookup-abel C4 = c3-1

abelianize : A4 → C3Group
abelianize g = lookup-abel (classify g)

c3Char : C3Group → Eisenstein
c3Char c3-1  = 1ᵉ
c3Char c3-a  = ωᵉ
c3Char c3-a² = ω²ᵉ

-- c3Char 是群同态 (9 case refl)
c3Char-hom : ∀ x y → c3Char (x ·₃ y) ≡ c3Char x *ᵉ c3Char y
c3Char-hom c3-1 c3-1 = refl
c3Char-hom c3-1 c3-a = refl
c3Char-hom c3-1 c3-a² = refl
c3Char-hom c3-a c3-1 = refl
c3Char-hom c3-a c3-a = refl
c3Char-hom c3-a c3-a² = refl
c3Char-hom c3-a² c3-1 = refl
c3Char-hom c3-a² c3-a = refl
c3Char-hom c3-a² c3-a² = refl

-- V1' 通过 Abel 化拉回 (逐共轭类, 无 with)
χ₁'-via-abelianization : ∀ (g : A4) → character V1' g ≡ c3Char (abelianize g)
χ₁'-via-abelianization g = charAt-abel (classify g)
  where
  charAt-abel : ∀ c → charAt V1' c ≡ c3Char (lookup-abel c)
  charAt-abel C1 = refl
  charAt-abel C2 = refl
  charAt-abel C3 = refl
  charAt-abel C4 = refl

-- Abel 化是群同态 (12×12 = 144 case 显式 refl:
--   _⊗_ = fromPerm(perm∘perm) 对具体元素经 with 归约, 无 perm-hom/函数 λ 绑定 —
--   后者在 Agda 2.9.0 触发 Substitute.hs 内部错误, 已由探针隔离)
abelianize-hom : ∀ g h → abelianize (g ⊗ h) ≡ abelianize g ·₃ abelianize h
abelianize-hom (Id) (Id) = refl
abelianize-hom (Id) (Rot (zero) (zero)) = refl
abelianize-hom (Id) (Rot (zero) (suc zero)) = refl
abelianize-hom (Id) (Rot (suc zero) (zero)) = refl
abelianize-hom (Id) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Id) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Id) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Id) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Id) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Id) (Flip (zero)) = refl
abelianize-hom (Id) (Flip (suc zero)) = refl
abelianize-hom (Id) (Flip (suc (suc zero))) = refl
abelianize-hom (Rot (zero) (zero)) (Id) = refl
abelianize-hom (Rot (zero) (zero)) (Rot (zero) (zero)) = refl
abelianize-hom (Rot (zero) (zero)) (Rot (zero) (suc zero)) = refl
abelianize-hom (Rot (zero) (zero)) (Rot (suc zero) (zero)) = refl
abelianize-hom (Rot (zero) (zero)) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Rot (zero) (zero)) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Rot (zero) (zero)) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Rot (zero) (zero)) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Rot (zero) (zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Rot (zero) (zero)) (Flip (zero)) = refl
abelianize-hom (Rot (zero) (zero)) (Flip (suc zero)) = refl
abelianize-hom (Rot (zero) (zero)) (Flip (suc (suc zero))) = refl
abelianize-hom (Rot (zero) (suc zero)) (Id) = refl
abelianize-hom (Rot (zero) (suc zero)) (Rot (zero) (zero)) = refl
abelianize-hom (Rot (zero) (suc zero)) (Rot (zero) (suc zero)) = refl
abelianize-hom (Rot (zero) (suc zero)) (Rot (suc zero) (zero)) = refl
abelianize-hom (Rot (zero) (suc zero)) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Rot (zero) (suc zero)) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Rot (zero) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Rot (zero) (suc zero)) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Rot (zero) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Rot (zero) (suc zero)) (Flip (zero)) = refl
abelianize-hom (Rot (zero) (suc zero)) (Flip (suc zero)) = refl
abelianize-hom (Rot (zero) (suc zero)) (Flip (suc (suc zero))) = refl
abelianize-hom (Rot (suc zero) (zero)) (Id) = refl
abelianize-hom (Rot (suc zero) (zero)) (Rot (zero) (zero)) = refl
abelianize-hom (Rot (suc zero) (zero)) (Rot (zero) (suc zero)) = refl
abelianize-hom (Rot (suc zero) (zero)) (Rot (suc zero) (zero)) = refl
abelianize-hom (Rot (suc zero) (zero)) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Rot (suc zero) (zero)) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Rot (suc zero) (zero)) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Rot (suc zero) (zero)) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Rot (suc zero) (zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Rot (suc zero) (zero)) (Flip (zero)) = refl
abelianize-hom (Rot (suc zero) (zero)) (Flip (suc zero)) = refl
abelianize-hom (Rot (suc zero) (zero)) (Flip (suc (suc zero))) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Id) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Rot (zero) (zero)) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Rot (zero) (suc zero)) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Rot (suc zero) (zero)) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Flip (zero)) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Flip (suc zero)) = refl
abelianize-hom (Rot (suc zero) (suc zero)) (Flip (suc (suc zero))) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Id) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Rot (zero) (zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Rot (zero) (suc zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Rot (suc zero) (zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Flip (zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Flip (suc zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (zero)) (Flip (suc (suc zero))) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Id) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Rot (zero) (zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Rot (zero) (suc zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc zero) (zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Flip (zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Flip (suc zero)) = refl
abelianize-hom (Rot (suc (suc zero)) (suc zero)) (Flip (suc (suc zero))) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Id) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Rot (zero) (zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Rot (zero) (suc zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Rot (suc zero) (zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Flip (zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Flip (suc zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (zero)) (Flip (suc (suc zero))) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Id) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (zero) (zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (zero) (suc zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc zero) (zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Flip (zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Flip (suc zero)) = refl
abelianize-hom (Rot (suc (suc (suc zero))) (suc zero)) (Flip (suc (suc zero))) = refl
abelianize-hom (Flip (zero)) (Id) = refl
abelianize-hom (Flip (zero)) (Rot (zero) (zero)) = refl
abelianize-hom (Flip (zero)) (Rot (zero) (suc zero)) = refl
abelianize-hom (Flip (zero)) (Rot (suc zero) (zero)) = refl
abelianize-hom (Flip (zero)) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Flip (zero)) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Flip (zero)) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Flip (zero)) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Flip (zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Flip (zero)) (Flip (zero)) = refl
abelianize-hom (Flip (zero)) (Flip (suc zero)) = refl
abelianize-hom (Flip (zero)) (Flip (suc (suc zero))) = refl
abelianize-hom (Flip (suc zero)) (Id) = refl
abelianize-hom (Flip (suc zero)) (Rot (zero) (zero)) = refl
abelianize-hom (Flip (suc zero)) (Rot (zero) (suc zero)) = refl
abelianize-hom (Flip (suc zero)) (Rot (suc zero) (zero)) = refl
abelianize-hom (Flip (suc zero)) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Flip (suc zero)) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Flip (suc zero)) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Flip (suc zero)) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Flip (suc zero)) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Flip (suc zero)) (Flip (zero)) = refl
abelianize-hom (Flip (suc zero)) (Flip (suc zero)) = refl
abelianize-hom (Flip (suc zero)) (Flip (suc (suc zero))) = refl
abelianize-hom (Flip (suc (suc zero))) (Id) = refl
abelianize-hom (Flip (suc (suc zero))) (Rot (zero) (zero)) = refl
abelianize-hom (Flip (suc (suc zero))) (Rot (zero) (suc zero)) = refl
abelianize-hom (Flip (suc (suc zero))) (Rot (suc zero) (zero)) = refl
abelianize-hom (Flip (suc (suc zero))) (Rot (suc zero) (suc zero)) = refl
abelianize-hom (Flip (suc (suc zero))) (Rot (suc (suc zero)) (zero)) = refl
abelianize-hom (Flip (suc (suc zero))) (Rot (suc (suc zero)) (suc zero)) = refl
abelianize-hom (Flip (suc (suc zero))) (Rot (suc (suc (suc zero))) (zero)) = refl
abelianize-hom (Flip (suc (suc zero))) (Rot (suc (suc (suc zero))) (suc zero)) = refl
abelianize-hom (Flip (suc (suc zero))) (Flip (zero)) = refl
abelianize-hom (Flip (suc (suc zero))) (Flip (suc zero)) = refl
abelianize-hom (Flip (suc (suc zero))) (Flip (suc (suc zero))) = refl

-- 三个一维特征标均为群同态 (genuine 1-dim representations)
-- V1: 平凡 (处处 1)
χ₁-multiplicative : ∀ g h → character V1 (g ⊗ h) ≡ character V1 g *ᵉ character V1 h
χ₁-multiplicative g h = begin
  character V1 (g ⊗ h)
    ≡⟨ χ₁-values (g ⊗ h) ⟩
  1ᵉ
    ≡⟨ sym one-times-one ⟩
  1ᵉ *ᵉ 1ᵉ
    ≡⟨ cong₂ _*ᵉ_ (sym (χ₁-values g)) (sym (χ₁-values h)) ⟩
  character V1 g *ᵉ character V1 h ∎
  where
  one-times-one : 1ᵉ *ᵉ 1ᵉ ≡ 1ᵉ
  one-times-one = refl

-- V1': 经 Abel 化拉回的 ω 特征标
χ₁'-multiplicative : ∀ g h → character V1' (g ⊗ h) ≡ character V1' g *ᵉ character V1' h
χ₁'-multiplicative g h = begin
  character V1' (g ⊗ h)
    ≡⟨ χ₁'-via-abelianization (g ⊗ h) ⟩
  c3Char (abelianize (g ⊗ h))
    ≡⟨ cong c3Char (abelianize-hom g h) ⟩
  c3Char (abelianize g ·₃ abelianize h)
    ≡⟨ c3Char-hom (abelianize g) (abelianize h) ⟩
  c3Char (abelianize g) *ᵉ c3Char (abelianize h)
    ≡⟨ cong₂ _*ᵉ_ (sym (χ₁'-via-abelianization g)) (sym (χ₁'-via-abelianization h)) ⟩
  character V1' g *ᵉ character V1' h ∎

-- V1'': ω² 特征标 (共轭拉回)
χ₁''-multiplicative : ∀ g h → character V1'' (g ⊗ h) ≡ character V1'' g *ᵉ character V1'' h
χ₁''-multiplicative g h = begin
  character V1'' (g ⊗ h)
    ≡⟨ χ₁''-is-conj-χ₁' (g ⊗ h) ⟩
  conjᵉ (character V1' (g ⊗ h))
    ≡⟨ cong conjᵉ (χ₁'-multiplicative g h) ⟩
  conjᵉ (character V1' g *ᵉ character V1' h)
    ≡⟨ conjᵉ-mul (character V1' g) (character V1' h) ⟩
  conjᵉ (character V1' g) *ᵉ conjᵉ (character V1' h)
    ≡⟨ cong₂ _*ᵉ_ (sym (χ₁''-is-conj-χ₁' g)) (sym (χ₁''-is-conj-χ₁' h)) ⟩
  character V1'' g *ᵉ character V1'' h ∎

--------------------------------------------------------------------------------
-- 8. 完备性定理
--------------------------------------------------------------------------------

theorem-dimension-sum-of-squares : dim V3 *N dim V3 +N dim V1 *N dim V1 +N dim V1' *N dim V1' +N dim V1'' *N dim V1'' ≡ 12
theorem-dimension-sum-of-squares = refl

theorem-class-count : classSize C1 +N classSize C2 +N classSize C3 +N classSize C4 ≡ 12
theorem-class-count = refl

-- 完备性配对: Σdᵢ² = Σ|C| = |A₄| = 12 (维数平方和 = 类大小和)
theorem-dim-sum-eq-class-sum :
  (dim V3 *N dim V3 +N dim V1 *N dim V1 +N dim V1' *N dim V1' +N dim V1'' *N dim V1'')
  ≡ (classSize C1 +N classSize C2 +N classSize C3 +N classSize C4)
theorem-dim-sum-eq-class-sum = refl

--------------------------------------------------------------------------------
-- 9. 连接物理: 三代费米子 = 三个一维特征标 + 三维标准表示
--    (代数层; A₄ 味对称 ↔ Altarelli-Feruglio 的物理对应为框架层解读)
--------------------------------------------------------------------------------

record FermionGenerations : Set where
  field
    leftDoublets  : A4Irrep
    rightSinglets : A4Irrep × A4Irrep × A4Irrep

standardFermionAssignment : FermionGenerations
standardFermionAssignment = record
  { leftDoublets  = V3
  ; rightSinglets = (V1 , V1'' , V1')  -- e^c, μ^c, τ^c
  }

-- 0 postulate.




