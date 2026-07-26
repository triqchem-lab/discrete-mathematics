{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.HomologyHarmonic
-- 同调代数与调和分析的浅层定理
--
-- MSC 55: 同调截断 — Δ³≡0 意味着高阶同调消失
-- MSC 42: 调和分析 — Euler 示性数、Plancherel 定理、卷积定理
--
-- 核心结果:
--   §1. 同调截断: Δ³≡0 → H^n = 0 for n ≥ 3
--   §2. Euler 示性数: χ(T⁶) = Σ(-1)^k C(6,k) = 0
--   §3. Plancherel 定理 (A₄): 特征标正交性 → 完备正交基
--   §4. 卷积定理 (Z/3Z): sum3(f*g) = sum3(f) · sum3(g) [DC 分量]
--   §5. Leibniz 规则: Δ(f*g) = f*(Δg) = (Δf)*g [非 DC 分量]
--
-- 依赖:
--   ProjectionDifferential: Δ³≡0, GF3Func, sum3, shift
--   DiscreteDE: Δⁿ, Δⁿ≥3≡0, Δ≡0→const
--   A4Representations: A4Irrep, ConjugacyClass, dim
--   Eisenstein: Z[ω] 算术
--
-- 0 postulate — 全部构造性证明, 穷举法优先
--------------------------------------------------------------------------------

module Sovereign.Applied.HomologyHarmonic where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (
  _≡_; refl; cong; sym; trans; module ≡-Reasoning)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc;
  ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕)
open import Sovereign.Algebra.ProjectionDifferential using (
  GF3Func; shift; Δ; sum3; Δ³≡0; Δ-const-zero; const-func)
open import Sovereign.Algebra.DiscreteDE using (
  Δⁿ; Δⁿ≥3≡0; Δ⁴≡0; Δ≡0→const)
open import Sovereign.Structology.A4Representations using (
  A4Irrep; V3; V1; V1'; V1'';
  ConjugacyClass; C1; C2; C3; C4;
  classSize; dim)
open import Sovereign.RootMath.Eisenstein using (
  Eisenstein; eis; 0ᵉ; 1ᵉ; ωᵉ; ω²ᵉ; -1ᵉ; 3ᵉ; _+ᵉ_; _*ᵉ_; conjᵉ)

open import Data.Integer using (+_; -[1+_])

--------------------------------------------------------------------------------
-- §1. 同调截断 — Δ³≡0 意味着高阶同调消失
--
-- 代数本质: Δ = S - I, 在 char 3 上 Δ³ = (S-I)³ = S³ - I = 0。
-- 连续微分 d³/dx³ 不恒为零 — 幂零截断是离散与连续的根本差异。
--
-- 同调推论:
--   im(Δ³) = {0}, 故三阶以上"边界群"平凡。
--   ker(Δ) = 常数函数 (H⁰ 的离散模拟)。
--   Δⁿ ≡ 0 对所有 n ≥ 3 (幂零性推广)。
--------------------------------------------------------------------------------

-- 定理 1.1: 三阶同调消失
-- Δ³f = 0 对所有 f — 直接引用已有定理
homology-vanishes-3 : ∀ (f : GF3Func) → Δ (Δ (Δ f)) ≡ (T₀ , T₀ , T₀)
homology-vanishes-3 = Δ³≡0

-- 定理 1.2: 高阶同调消失 (n ≥ 3)
-- Δⁿf = 0 对所有 n ≥ 3 和所有 f
homology-vanishes-higher : ∀ n f → Δⁿ (3 + n) f ≡ (T₀ , T₀ , T₀)
homology-vanishes-higher = Δⁿ≥3≡0

-- 定理 1.3: 四阶同调消失 (具体实例)
homology-vanishes-4 : ∀ f → Δⁿ 4 f ≡ (T₀ , T₀ , T₀)
homology-vanishes-4 = Δ⁴≡0

-- 定理 1.4: im(Δ³) = {0} — 三阶边界群平凡
-- Δ³ 将一切映射为零, 故像集仅含零元素
image-Δ³-trivial : ∀ f → Δⁿ 3 f ≡ (T₀ , T₀ , T₀)
image-Δ³-trivial f = Δ³≡0 f

-- 定理 1.5: ker(Δ) = 常数函数
-- Δf = 0 当且仅当 f 是常数 (f₀ = f₁ = f₂)
-- 这是 H⁰ 的离散模拟: 零阶同调 = 常数函数空间
ker-Δ-constants : ∀ f → Δ f ≡ (T₀ , T₀ , T₀) →
  Σ Trit (λ c → f ≡ (c , c , c))
ker-Δ-constants = Δ≡0→const

-- 定理 1.6: 链复形条件
-- Δ³≡0 保证 d₀ = Δ, d₁ = Δ² 满足 d₀ ∘ d₁ = 0
-- 即 im(Δ²) ⊆ ker(Δ), 构成合法链复形
chain-complex-d₀∘d₁ : ∀ f → Δ (Δ (Δ f)) ≡ (T₀ , T₀ , T₀)
chain-complex-d₀∘d₁ = Δ³≡0

-- 定理 1.7: 常数函数被 Δ 消灭
-- 常数函数在差分下为零 — 离散版 "常数的导数为零"
const-in-kernel : ∀ s → Δ (const-func s) ≡ (T₀ , T₀ , T₀)
const-in-kernel = Δ-const-zero

--------------------------------------------------------------------------------
-- §2. Euler 示性数 — χ(T⁶) = 0
--
-- T⁶ = (S¹)⁶ 是 6 维环面。
-- Betti 数: β_k = C(6,k) (二项式系数)
-- Euler 示性数: χ = Σ(-1)^k β_k = (1-1)⁶ = 0
--
-- 离散验证: 偶数阶 Betti 数之和 = 奇数阶 Betti 数之和 = 32
--------------------------------------------------------------------------------

-- Betti 数 of T⁶: β_k = C(6,k)
β₀ : ℕ; β₀ = 1    -- C(6,0) = 1
β₁ : ℕ; β₁ = 6    -- C(6,1) = 6
β₂ : ℕ; β₂ = 15   -- C(6,2) = 15
β₃ : ℕ; β₃ = 20   -- C(6,3) = 20
β₄ : ℕ; β₄ = 15   -- C(6,4) = 15
β₅ : ℕ; β₅ = 6    -- C(6,5) = 6
β₆ : ℕ; β₆ = 1    -- C(6,6) = 1

-- 定理 2.1: 偶数阶 Betti 数之和 = 32
euler-even-sum : β₀ + β₂ + β₄ + β₆ ≡ 32
euler-even-sum = refl

-- 定理 2.2: 奇数阶 Betti 数之和 = 32
euler-odd-sum : β₁ + β₃ + β₅ ≡ 32
euler-odd-sum = refl

-- 定理 2.3: χ(T⁶) = 0
-- 偶数阶和 = 奇数阶和, 故交替和为零
euler-characteristic : β₀ + β₂ + β₄ + β₆ ≡ β₁ + β₃ + β₅
euler-characteristic = refl  -- 32 ≡ 32

-- 定理 2.4: 二项式系数验证 C(6,2) = 15
binom-6-2 : 6 * 5 ≡ 2 * 15
binom-6-2 = refl  -- 30 ≡ 30

-- 定理 2.5: 二项式系数验证 C(6,3) = 20
binom-6-3 : 6 * 5 * 4 ≡ 6 * 20
binom-6-3 = refl  -- 120 ≡ 120

-- 定理 2.6: Betti 数总和 = 2⁶ = 64
betti-total : β₀ + β₁ + β₂ + β₃ + β₄ + β₅ + β₆ ≡ 64
betti-total = refl

-- 定理 2.7: 维数平方和 = |A₄| = 12 (与 §3 Plancherel 的连接)
-- A₄ 的不可约表示维数: 3, 1, 1, 1
-- 3² + 1² + 1² + 1² = 12 = |A₄|
dim-sq-sum : 3 * 3 + 1 * 1 + 1 * 1 + 1 * 1 ≡ 12
dim-sq-sum = refl

--------------------------------------------------------------------------------
-- §3. Plancherel 定理 (A₄ 版本) — 特征标正交性
--
-- A₄ 有 4 个共轭类 C₁(1), C₂(4), C₃(4), C₄(3) 和 4 个不可约表示。
-- 特征标表:
--        C₁  C₂  C₃  C₄
--   V₃:   3   0   0  -1
--   V₁:   1   1   1   1
--   V₁':  1   ω   ω²  1
--   V₁'': 1   ω²  ω   1
--
-- Plancherel/正交性:
--   ⟨χ_ρ, χ_σ⟩ = Σ_C |C| · χ_ρ(C) · conj(χ_σ(C)) = |G| · δ_{ρσ}
--
-- 全部通过 Eisenstein 整数 Z[ω] 上的穷举计算验证。
--------------------------------------------------------------------------------

-- 特征标值查表 (按共轭类, 不依赖 A₄ 元素编码)
charVal : A4Irrep → ConjugacyClass → Eisenstein
charVal V3 C1 = 3ᵉ
charVal V3 C2 = 0ᵉ
charVal V3 C3 = 0ᵉ
charVal V3 C4 = -1ᵉ
charVal V1 _  = 1ᵉ
charVal V1' C1 = 1ᵉ
charVal V1' C2 = ωᵉ
charVal V1' C3 = ω²ᵉ
charVal V1' C4 = 1ᵉ
charVal V1'' C1 = 1ᵉ
charVal V1'' C2 = ω²ᵉ
charVal V1'' C3 = ωᵉ
charVal V1'' C4 = 1ᵉ

-- 共轭类大小的 Eisenstein 表示
classSizeE : ConjugacyClass → Eisenstein
classSizeE C1 = 1ᵉ
classSizeE C2 = eis (+ 4) (+ 0)
classSizeE C3 = eis (+ 4) (+ 0)
classSizeE C4 = eis (+ 3) (+ 0)

-- |G| = 12 的 Eisenstein 表示
12ᵉ : Eisenstein
12ᵉ = eis (+ 12) (+ 0)

-- 加权特征标内积:
-- ⟨χ_ρ, χ_σ⟩ = Σ_C |C| · χ_ρ(C) · conj(χ_σ(C))
charInner : A4Irrep → A4Irrep → Eisenstein
charInner ρ σ =
  (classSizeE C1 *ᵉ charVal ρ C1 *ᵉ conjᵉ (charVal σ C1)) +ᵉ
  (classSizeE C2 *ᵉ charVal ρ C2 *ᵉ conjᵉ (charVal σ C2)) +ᵉ
  (classSizeE C3 *ᵉ charVal ρ C3 *ᵉ conjᵉ (charVal σ C3)) +ᵉ
  (classSizeE C4 *ᵉ charVal ρ C4 *ᵉ conjᵉ (charVal σ C4))

-- 定理 3.1-3.4: Plancherel 对角 — ⟨χ_ρ, χ_ρ⟩ = |G| = 12
-- 每个不可约表示的特征标自内积等于群阶

plancherel-V3 : charInner V3 V3 ≡ 12ᵉ
plancherel-V3 = refl  -- 1·9 + 4·0 + 4·0 + 3·1 = 12

plancherel-V1 : charInner V1 V1 ≡ 12ᵉ
plancherel-V1 = refl  -- 1·1 + 4·1 + 4·1 + 3·1 = 12

plancherel-V1' : charInner V1' V1' ≡ 12ᵉ
plancherel-V1' = refl  -- 1·1 + 4·|ω|² + 4·|ω²|² + 3·1 = 12

plancherel-V1'' : charInner V1'' V1'' ≡ 12ᵉ
plancherel-V1'' = refl  -- 同 V1' (共轭对称)

-- 定理 3.5-3.10: Plancherel 正交 — ⟨χ_ρ, χ_σ⟩ = 0 for ρ ≠ σ
-- 不同不可约表示的特征标正交

plancherel-V3-V1 : charInner V3 V1 ≡ 0ᵉ
plancherel-V3-V1 = refl  -- 1·3·1 + 4·0·1 + 4·0·1 + 3·(-1)·1 = 3-3 = 0

plancherel-V3-V1' : charInner V3 V1' ≡ 0ᵉ
plancherel-V3-V1' = refl  -- 1·3·1 + 0 + 0 + 3·(-1)·1 = 0

plancherel-V3-V1'' : charInner V3 V1'' ≡ 0ᵉ
plancherel-V3-V1'' = refl  -- 同 V3-V1' (共轭对称)

plancherel-V1-V1' : charInner V1 V1' ≡ 0ᵉ
plancherel-V1-V1' = refl  -- 1 + 4ω² + 4ω + 3 = 4 + 4(ω+ω²) = 4-4 = 0

plancherel-V1-V1'' : charInner V1 V1'' ≡ 0ᵉ
plancherel-V1-V1'' = refl  -- 1 + 4ω + 4ω² + 3 = 0 (同上)

plancherel-V1'-V1'' : charInner V1' V1'' ≡ 0ᵉ
plancherel-V1'-V1'' = refl  -- 1 + 4ω·ω + 4ω²·ω² + 3 = 1+4ω²+4ω+3 = 0

-- 定理 3.11: 维数公式 Σ dim(ρ)² = |G| = 12
-- Plancherel 定理的维数推论
plancherel-dim-formula :
  dim V3 * dim V3 + dim V1 * dim V1 + dim V1' * dim V1' + dim V1'' * dim V1'' ≡ 12
plancherel-dim-formula = refl  -- 9 + 1 + 1 + 1 = 12

-- 定理 3.12: 共轭类大小之和 = |G| = 12
class-size-sum : classSize C1 + classSize C2 + classSize C3 + classSize C4 ≡ 12
class-size-sum = refl  -- 1 + 4 + 4 + 3 = 12

--------------------------------------------------------------------------------
-- §4. 卷积定理 (Z/3Z 版本)
--
-- GF3Func = (Trit × Trit × Trit) 是 Z/3Z 上 GF(3)-值函数空间。
-- 循环卷积: (f*g)(x) = Σ_y f(y)·g(x-y)
--
-- 卷积定理 (DC 分量):
--   sum3(f*g) = sum3(f) · sum3(g)
--   即 "增广映射" sum3 是环同态 (GF3Func, *, +) → (GF(3), ·, +)
--
-- 这是有限群上 Plancherel/卷积定理的最简非平凡实例:
-- 在 Z/3Z 的 Abel 化上, 卷积定理的 k=0 分量。
--------------------------------------------------------------------------------

-- 逐点加法
infixl 20 _⊕f_
_⊕f_ : GF3Func → GF3Func → GF3Func
(a₀ , a₁ , a₂) ⊕f (b₀ , b₁ , b₂) = (a₀ ⊕ b₀ , a₁ ⊕ b₁ , a₂ ⊕ b₂)

-- 标量乘法
infixr 25 _⊗f_
_⊗f_ : Trit → GF3Func → GF3Func
s ⊗f (a₀ , a₁ , a₂) = (s ⊗ a₀ , s ⊗ a₁ , s ⊗ a₂)

-- 循环卷积: (f*g)(x) = Σ_y f(y)·g(x⊖y)
-- 在 Z/3Z 上展开:
--   (f*g)(0) = f₀g₀ + f₁g₂ + f₂g₁  (y=0: x-y=0; y=1: x-y=2; y=2: x-y=1)
--   (f*g)(1) = f₀g₁ + f₁g₀ + f₂g₂
--   (f*g)(2) = f₀g₂ + f₁g₁ + f₂g₀
conv : GF3Func → GF3Func → GF3Func
conv (f₀ , f₁ , f₂) (g₀ , g₁ , g₂) =
  ( ((f₀ ⊗ g₀) ⊕ (f₁ ⊗ g₂)) ⊕ (f₂ ⊗ g₁)
  , ((f₀ ⊗ g₁) ⊕ (f₁ ⊗ g₀)) ⊕ (f₂ ⊗ g₂)
  , ((f₀ ⊗ g₂) ⊕ (f₁ ⊗ g₁)) ⊕ (f₂ ⊗ g₀)
  )

-- Delta 函数 (卷积单位元)
δ : GF3Func
δ = (T₁ , T₀ , T₀)

-- 零函数
zero-func : GF3Func
zero-func = (T₀ , T₀ , T₀)

--------------------------------------------------------------------------------
-- §4a. 辅助引理 — GF(3) 加法重排
--------------------------------------------------------------------------------

-- 三元组等式构造
triple-≡ : ∀ {a b c a' b' c' : Trit} →
  a ≡ a' → b ≡ b' → c ≡ c' → (a , b , c) ≡ (a' , b' , c')
triple-≡ refl refl refl = refl

-- 加法交换重排: (a+b)+(c+d) = (a+c)+(b+d)
-- 证明: 结合律 + 交换律, 6 步
⊕-interchange : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
⊕-interchange a b c d = begin
  (a ⊕ b) ⊕ (c ⊕ d)
    ≡⟨ ⊕-assoc a b (c ⊕ d) ⟩
  a ⊕ (b ⊕ (c ⊕ d))
    ≡⟨ cong (λ x → a ⊕ x) (sym (⊕-assoc b c d)) ⟩
  a ⊕ ((b ⊕ c) ⊕ d)
    ≡⟨ cong (λ x → a ⊕ x) (cong (_⊕ d) (⊕-comm b c)) ⟩
  a ⊕ ((c ⊕ b) ⊕ d)
    ≡⟨ cong (λ x → a ⊕ x) (⊕-assoc c b d) ⟩
  a ⊕ (c ⊕ (b ⊕ d))
    ≡⟨ sym (⊕-assoc a c (b ⊕ d)) ⟩
  (a ⊕ c) ⊕ (b ⊕ d)
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §4b. sum3 的代数性质
--------------------------------------------------------------------------------

-- 定理 4.1: sum3 保持逐点加法
-- sum3(f + g) = sum3(f) + sum3(g)
-- 证明: 两次 ⊕-interchange
sum3-⊕f : ∀ f g → sum3 (f ⊕f g) ≡ sum3 f ⊕ sum3 g
sum3-⊕f (a₀ , a₁ , a₂) (b₀ , b₁ , b₂) =
  trans (cong (_⊕ (a₂ ⊕ b₂)) (⊕-interchange a₀ b₀ a₁ b₁))
        (⊕-interchange (a₀ ⊕ a₁) (b₀ ⊕ b₁) a₂ b₂)

-- 定理 4.2: sum3 与标量乘法交换
-- sum3(s · g) = s · sum3(g)
-- 证明: 分配律 ⊗-distribˡ-⊕
sum3-⊗f : ∀ s g → sum3 (s ⊗f g) ≡ s ⊗ sum3 g
sum3-⊗f s (g₀ , g₁ , g₂) =
  sym (trans (⊗-distribˡ-⊕ s (g₀ ⊕ g₁) g₂)
             (cong (_⊕ (s ⊗ g₂)) (⊗-distribˡ-⊕ s g₀ g₁)))

-- 定理 4.3: sum3 在移位下不变
-- sum3(shift f) = sum3(f)
-- 证明: 结合律 + 交换律, 4 步
sum3-shift : ∀ f → sum3 (shift f) ≡ sum3 f
sum3-shift (f₀ , f₁ , f₂) = begin
  (f₁ ⊕ f₂) ⊕ f₀
    ≡⟨ ⊕-assoc f₁ f₂ f₀ ⟩
  f₁ ⊕ (f₂ ⊕ f₀)
    ≡⟨ cong (f₁ ⊕_) (⊕-comm f₂ f₀) ⟩
  f₁ ⊕ (f₀ ⊕ f₂)
    ≡⟨ sym (⊕-assoc f₁ f₀ f₂) ⟩
  (f₁ ⊕ f₀) ⊕ f₂
    ≡⟨ cong (_⊕ f₂) (⊕-comm f₁ f₀) ⟩
  (f₀ ⊕ f₁) ⊕ f₂
  ∎
  where open ≡-Reasoning

-- 定理 4.4: sum3 在二次移位下不变
sum3-shift² : ∀ f → sum3 (shift (shift f)) ≡ sum3 f
sum3-shift² f = trans (sum3-shift (shift f)) (sum3-shift f)

--------------------------------------------------------------------------------
-- §4c. 卷积定理
--------------------------------------------------------------------------------

-- 定理 4.5: δ 是卷积左单位元
-- δ * g = g
-- 证明: T₁⊗x = x (⊗-identityˡ), T₀⊗x = T₀ (定义归约), x⊕T₀ = x (⊕-identityʳ)
conv-δ-left : ∀ g → conv δ g ≡ g
conv-δ-left (g₀ , g₁ , g₂) = triple-≡ p₀ p₁ p₂
  where
    open ≡-Reasoning
    p₀ : ((T₁ ⊗ g₀) ⊕ T₀) ⊕ T₀ ≡ g₀
    p₀ = begin
      ((T₁ ⊗ g₀) ⊕ T₀) ⊕ T₀
        ≡⟨ cong (λ x → (x ⊕ T₀) ⊕ T₀) (⊗-identityˡ g₀) ⟩
      (g₀ ⊕ T₀) ⊕ T₀
        ≡⟨ ⊕-identityʳ (g₀ ⊕ T₀) ⟩
      g₀ ⊕ T₀
        ≡⟨ ⊕-identityʳ g₀ ⟩
      g₀ ∎
    p₁ : ((T₁ ⊗ g₁) ⊕ T₀) ⊕ T₀ ≡ g₁
    p₁ = begin
      ((T₁ ⊗ g₁) ⊕ T₀) ⊕ T₀
        ≡⟨ cong (λ x → (x ⊕ T₀) ⊕ T₀) (⊗-identityˡ g₁) ⟩
      (g₁ ⊕ T₀) ⊕ T₀
        ≡⟨ ⊕-identityʳ (g₁ ⊕ T₀) ⟩
      g₁ ⊕ T₀
        ≡⟨ ⊕-identityʳ g₁ ⟩
      g₁ ∎
    p₂ : ((T₁ ⊗ g₂) ⊕ T₀) ⊕ T₀ ≡ g₂
    p₂ = begin
      ((T₁ ⊗ g₂) ⊕ T₀) ⊕ T₀
        ≡⟨ cong (λ x → (x ⊕ T₀) ⊕ T₀) (⊗-identityˡ g₂) ⟩
      (g₂ ⊕ T₀) ⊕ T₀
        ≡⟨ ⊕-identityʳ (g₂ ⊕ T₀) ⟩
      g₂ ⊕ T₀
        ≡⟨ ⊕-identityʳ g₂ ⟩
      g₂ ∎

-- 定理 4.6: 零函数消灭卷积
-- 0 * g = 0
conv-zero-left : ∀ g → conv zero-func g ≡ zero-func
conv-zero-left (g₀ , g₁ , g₂) = refl

-- 定理 4.7: 卷积分解为移位叠加
-- conv f g = f₀·g + f₁·shift²(g) + f₂·shift(g)
conv-decomp : ∀ f₀ f₁ f₂ g₀ g₁ g₂ →
  conv (f₀ , f₁ , f₂) (g₀ , g₁ , g₂) ≡
  ((f₀ ⊗f (g₀ , g₁ , g₂)) ⊕f
   (f₁ ⊗f (g₂ , g₀ , g₁)) ⊕f
   (f₂ ⊗f (g₁ , g₂ , g₀)))
conv-decomp f₀ f₁ f₂ g₀ g₁ g₂ = refl

-- 定理 4.8: 卷积定理 (DC 分量 / 增广同态)
-- sum3(f * g) = sum3(f) · sum3(g)
--
-- 证明策略:
--   1. 分解 conv f g = f₀·g + f₁·shift²(g) + f₂·shift(g)
--   2. sum3 保持加法 (sum3-⊕f)
--   3. sum3 与标量乘法交换 (sum3-⊗f)
--   4. sum3 在移位下不变 (sum3-shift)
--   5. 分配律提取公因子 (⊗-distribʳ-⊕)
augment-conv : ∀ f g → sum3 (conv f g) ≡ sum3 f ⊗ sum3 g
augment-conv (f₀ , f₁ , f₂) (g₀ , g₁ , g₂) = begin
  sum3 (conv (f₀ , f₁ , f₂) (g₀ , g₁ , g₂))
    ≡⟨ cong sum3 (conv-decomp f₀ f₁ f₂ g₀ g₁ g₂) ⟩
  sum3 ((f₀ ⊗f (g₀ , g₁ , g₂)) ⊕f (f₁ ⊗f (g₂ , g₀ , g₁)) ⊕f (f₂ ⊗f (g₁ , g₂ , g₀)))
    ≡⟨ sum3-⊕f ((f₀ ⊗f (g₀ , g₁ , g₂)) ⊕f (f₁ ⊗f (g₂ , g₀ , g₁)))
               (f₂ ⊗f (g₁ , g₂ , g₀)) ⟩
  sum3 ((f₀ ⊗f (g₀ , g₁ , g₂)) ⊕f (f₁ ⊗f (g₂ , g₀ , g₁)))
    ⊕ sum3 (f₂ ⊗f (g₁ , g₂ , g₀))
    ≡⟨ cong (_⊕ sum3 (f₂ ⊗f (g₁ , g₂ , g₀)))
            (sum3-⊕f (f₀ ⊗f (g₀ , g₁ , g₂)) (f₁ ⊗f (g₂ , g₀ , g₁))) ⟩
  (sum3 (f₀ ⊗f (g₀ , g₁ , g₂)) ⊕ sum3 (f₁ ⊗f (g₂ , g₀ , g₁)))
    ⊕ sum3 (f₂ ⊗f (g₁ , g₂ , g₀))
    ≡⟨ cong (λ x → (x ⊕ sum3 (f₁ ⊗f (g₂ , g₀ , g₁)))
                    ⊕ sum3 (f₂ ⊗f (g₁ , g₂ , g₀)))
            (sum3-⊗f f₀ (g₀ , g₁ , g₂)) ⟩
  ((f₀ ⊗ sum3 (g₀ , g₁ , g₂)) ⊕ sum3 (f₁ ⊗f (g₂ , g₀ , g₁)))
    ⊕ sum3 (f₂ ⊗f (g₁ , g₂ , g₀))
    ≡⟨ cong (λ x → ((f₀ ⊗ sum3 (g₀ , g₁ , g₂)) ⊕ x)
                    ⊕ sum3 (f₂ ⊗f (g₁ , g₂ , g₀)))
            (sum3-⊗f f₁ (g₂ , g₀ , g₁)) ⟩
  ((f₀ ⊗ sum3 (g₀ , g₁ , g₂)) ⊕ (f₁ ⊗ sum3 (g₂ , g₀ , g₁)))
    ⊕ sum3 (f₂ ⊗f (g₁ , g₂ , g₀))
    ≡⟨ cong (λ x → ((f₀ ⊗ sum3 (g₀ , g₁ , g₂)) ⊕ (f₁ ⊗ x))
                    ⊕ sum3 (f₂ ⊗f (g₁ , g₂ , g₀)))
            (sum3-shift² (g₀ , g₁ , g₂)) ⟩
  ((f₀ ⊗ sum3 (g₀ , g₁ , g₂)) ⊕ (f₁ ⊗ sum3 (g₀ , g₁ , g₂)))
    ⊕ sum3 (f₂ ⊗f (g₁ , g₂ , g₀))
    ≡⟨ cong (λ x → ((f₀ ⊗ sum3 (g₀ , g₁ , g₂)) ⊕ (f₁ ⊗ sum3 (g₀ , g₁ , g₂)))
                    ⊕ x)
            (sum3-⊗f f₂ (g₁ , g₂ , g₀)) ⟩
  ((f₀ ⊗ sum3 (g₀ , g₁ , g₂)) ⊕ (f₁ ⊗ sum3 (g₀ , g₁ , g₂)))
    ⊕ (f₂ ⊗ sum3 (g₁ , g₂ , g₀))
    ≡⟨ cong (λ x → ((f₀ ⊗ sum3 (g₀ , g₁ , g₂)) ⊕ (f₁ ⊗ sum3 (g₀ , g₁ , g₂)))
                    ⊕ (f₂ ⊗ x))
            (sum3-shift (g₀ , g₁ , g₂)) ⟩
  ((f₀ ⊗ sum3 (g₀ , g₁ , g₂)) ⊕ (f₁ ⊗ sum3 (g₀ , g₁ , g₂)))
    ⊕ (f₂ ⊗ sum3 (g₀ , g₁ , g₂))
    ≡⟨ cong (_⊕ (f₂ ⊗ sum3 (g₀ , g₁ , g₂)))
            (sym (⊗-distribʳ-⊕ f₀ f₁ (sum3 (g₀ , g₁ , g₂)))) ⟩
  ((f₀ ⊕ f₁) ⊗ sum3 (g₀ , g₁ , g₂))
    ⊕ (f₂ ⊗ sum3 (g₀ , g₁ , g₂))
    ≡⟨ sym (⊗-distribʳ-⊕ (f₀ ⊕ f₁) f₂ (sum3 (g₀ , g₁ , g₂))) ⟩
  ((f₀ ⊕ f₁) ⊕ f₂) ⊗ ((g₀ ⊕ g₁) ⊕ g₂)
  ∎
  where open ≡-Reasoning

-- 定理 4.9: δ 的增广同态验证 (具体实例)
-- sum3(δ * g) = sum3(δ) · sum3(g) = 1 · sum3(g) = sum3(g)
augment-δ : ∀ g → sum3 (conv δ g) ≡ sum3 δ ⊗ sum3 g
augment-δ g = trans (cong sum3 (conv-δ-left g)) (sym (⊗-identityˡ (sum3 g)))

-- 定理 4.10: 零函数的增广同态验证 (具体实例)
-- sum3(0 * g) = 0 = sum3(0) · sum3(g)
augment-zero : ∀ g → sum3 (conv zero-func g) ≡ sum3 zero-func ⊗ sum3 g
augment-zero g = refl

--------------------------------------------------------------------------------
-- §5. 差分-卷积交换律 — Leibniz 规则
--
-- GF(3) 上不存在本原三次单位根 (GF(3)* ≅ C₂, 3∤2),
-- 因此标准 DFT 卷积定理 f̂_k(g*h) = f̂_k(g)·f̂_k(h) 对 k=1,2 不成立。
--
-- 替代方案: 证明差分算子 Δ 与卷积交换:
--   Δ(f*g) = f*(Δg) = (Δf)*g
--
-- 代数本质: Δ = S - I, 而 S(f*g) = (Sf)*g (移位与卷积交换),
-- 故 Δ 作为 S 的多项式也与卷积交换。
--
-- 这是离散微积分的基本定理: 差分是卷积代数的导子。
-- 比 DFT 卷积定理更基础 — 它不依赖单位根的存在。
--
-- 频率解释:
--   DC 分量 (k=0): sum3(f*g) = sum3(f)·sum3(g) (§4, 增广同态)
--   非 DC 分量: Δ(f*g) = f*(Δg) (本节, Leibniz 规则)
--   两者合起来完全刻画了 Z/3Z 上卷积的频谱结构:
--   Δ²f = (sum3 f, sum3 f, sum3 f) 将 DC 分量提取为常数,
--   Δf 捕获全部非 DC 信息 (因为 Δ³≡0, 没有更高阶分量)。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §5a. 辅助引理 — GF(3) 加法/取反重排
--------------------------------------------------------------------------------

-- 三元加法循环旋转: (a+b)+c = (b+c)+a
⊕-rotate₃ : ∀ a b c → (a ⊕ b) ⊕ c ≡ (b ⊕ c) ⊕ a
⊕-rotate₃ a b c = trans (⊕-assoc a b c) (⊕-comm a (b ⊕ c))

-- 内层交换: (a+b)+c = (a+c)+b
⊕-swap-inner : ∀ a b c → (a ⊕ b) ⊕ c ≡ (a ⊕ c) ⊕ b
⊕-swap-inner a b c = begin
  (a ⊕ b) ⊕ c
    ≡⟨ ⊕-assoc a b c ⟩
  a ⊕ (b ⊕ c)
    ≡⟨ cong (a ⊕_) (⊕-comm b c) ⟩
  a ⊕ (c ⊕ b)
    ≡⟨ sym (⊕-assoc a c b) ⟩
  (a ⊕ c) ⊕ b
  ∎
  where open ≡-Reasoning

-- negate = 乘以 2 (GF(3) 中 -1 ≡ 2)
negate-≡-⊗₂ : ∀ x → negate x ≡ T₂ ⊗ x
negate-≡-⊗₂ T₀ = refl
negate-≡-⊗₂ T₁ = refl
negate-≡-⊗₂ T₂ = refl

-- negate 保持加法: -(a+b) = (-a)+(-b)
-- 证明: negate = T₂⊗_, 然后用分配律
negate-⊕ : ∀ a b → negate (a ⊕ b) ≡ negate a ⊕ negate b
negate-⊕ a b rewrite negate-≡-⊗₂ (a ⊕ b) | negate-≡-⊗₂ a | negate-≡-⊗₂ b =
  ⊗-distribˡ-⊕ T₂ a b

-- negate 与标量乘法交换: -(s·x) = s·(-x)
-- 证明: T₂⊗(s⊗x) = (T₂⊗s)⊗x = (s⊗T₂)⊗x = s⊗(T₂⊗x)
negate-⊗-scalar : ∀ s x → negate (s ⊗ x) ≡ s ⊗ negate x
negate-⊗-scalar s x = begin
  negate (s ⊗ x)
    ≡⟨ negate-≡-⊗₂ (s ⊗ x) ⟩
  T₂ ⊗ (s ⊗ x)
    ≡⟨ sym (⊗-assoc T₂ s x) ⟩
  (T₂ ⊗ s) ⊗ x
    ≡⟨ cong (_⊗ x) (⊗-comm T₂ s) ⟩
  (s ⊗ T₂) ⊗ x
    ≡⟨ ⊗-assoc s T₂ x ⟩
  s ⊗ (T₂ ⊗ x)
    ≡⟨ cong (s ⊗_) (sym (negate-≡-⊗₂ x)) ⟩
  s ⊗ negate x
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §5b. Δ 的线性与移位交换性
--------------------------------------------------------------------------------

-- 定理 5.1: Δ 保持逐点加法 (线性)
-- Δ(f + g) = Δf + Δg
-- 证明: negate-⊕ + ⊕-interchange
Δ-linear : ∀ f g → Δ (f ⊕f g) ≡ Δ f ⊕f Δ g
Δ-linear (a₀ , a₁ , a₂) (b₀ , b₁ , b₂) = triple-≡ p₀ p₁ p₂
  where
    open ≡-Reasoning
    p₀ : (a₁ ⊕ b₁) ⊕ negate (a₀ ⊕ b₀) ≡ (a₁ ⊕ negate a₀) ⊕ (b₁ ⊕ negate b₀)
    p₀ = begin
      (a₁ ⊕ b₁) ⊕ negate (a₀ ⊕ b₀)
        ≡⟨ cong ((a₁ ⊕ b₁) ⊕_) (negate-⊕ a₀ b₀) ⟩
      (a₁ ⊕ b₁) ⊕ (negate a₀ ⊕ negate b₀)
        ≡⟨ ⊕-interchange a₁ b₁ (negate a₀) (negate b₀) ⟩
      (a₁ ⊕ negate a₀) ⊕ (b₁ ⊕ negate b₀)
        ∎
    p₁ : (a₂ ⊕ b₂) ⊕ negate (a₁ ⊕ b₁) ≡ (a₂ ⊕ negate a₁) ⊕ (b₂ ⊕ negate b₁)
    p₁ = begin
      (a₂ ⊕ b₂) ⊕ negate (a₁ ⊕ b₁)
        ≡⟨ cong ((a₂ ⊕ b₂) ⊕_) (negate-⊕ a₁ b₁) ⟩
      (a₂ ⊕ b₂) ⊕ (negate a₁ ⊕ negate b₁)
        ≡⟨ ⊕-interchange a₂ b₂ (negate a₁) (negate b₁) ⟩
      (a₂ ⊕ negate a₁) ⊕ (b₂ ⊕ negate b₁)
        ∎
    p₂ : (a₀ ⊕ b₀) ⊕ negate (a₂ ⊕ b₂) ≡ (a₀ ⊕ negate a₂) ⊕ (b₀ ⊕ negate b₂)
    p₂ = begin
      (a₀ ⊕ b₀) ⊕ negate (a₂ ⊕ b₂)
        ≡⟨ cong ((a₀ ⊕ b₀) ⊕_) (negate-⊕ a₂ b₂) ⟩
      (a₀ ⊕ b₀) ⊕ (negate a₂ ⊕ negate b₂)
        ≡⟨ ⊕-interchange a₀ b₀ (negate a₂) (negate b₂) ⟩
      (a₀ ⊕ negate a₂) ⊕ (b₀ ⊕ negate b₂)
        ∎

-- 定理 5.2: Δ 与标量乘法交换
-- Δ(s · g) = s · Δg
-- 证明: negate-⊗-scalar + 分配律
Δ-scalar-comm : ∀ s g → Δ (s ⊗f g) ≡ s ⊗f Δ g
Δ-scalar-comm s (g₀ , g₁ , g₂) = triple-≡ p₀ p₁ p₂
  where
    open ≡-Reasoning
    p₀ : (s ⊗ g₁) ⊕ negate (s ⊗ g₀) ≡ s ⊗ (g₁ ⊕ negate g₀)
    p₀ = begin
      (s ⊗ g₁) ⊕ negate (s ⊗ g₀)
        ≡⟨ cong ((s ⊗ g₁) ⊕_) (negate-⊗-scalar s g₀) ⟩
      (s ⊗ g₁) ⊕ (s ⊗ negate g₀)
        ≡⟨ sym (⊗-distribˡ-⊕ s g₁ (negate g₀)) ⟩
      s ⊗ (g₁ ⊕ negate g₀)
        ∎
    p₁ : (s ⊗ g₂) ⊕ negate (s ⊗ g₁) ≡ s ⊗ (g₂ ⊕ negate g₁)
    p₁ = begin
      (s ⊗ g₂) ⊕ negate (s ⊗ g₁)
        ≡⟨ cong ((s ⊗ g₂) ⊕_) (negate-⊗-scalar s g₁) ⟩
      (s ⊗ g₂) ⊕ (s ⊗ negate g₁)
        ≡⟨ sym (⊗-distribˡ-⊕ s g₂ (negate g₁)) ⟩
      s ⊗ (g₂ ⊕ negate g₁)
        ∎
    p₂ : (s ⊗ g₀) ⊕ negate (s ⊗ g₂) ≡ s ⊗ (g₀ ⊕ negate g₂)
    p₂ = begin
      (s ⊗ g₀) ⊕ negate (s ⊗ g₂)
        ≡⟨ cong ((s ⊗ g₀) ⊕_) (negate-⊗-scalar s g₂) ⟩
      (s ⊗ g₀) ⊕ (s ⊗ negate g₂)
        ≡⟨ sym (⊗-distribˡ-⊕ s g₀ (negate g₂)) ⟩
      s ⊗ (g₀ ⊕ negate g₂)
        ∎

-- 定理 5.3: Δ 与移位交换
-- Δ(shift g) = shift(Δg)
-- 证明: 定义归约 (refl) — 两者展开为相同的三元组
Δ-shift-comm : ∀ g → Δ (shift g) ≡ shift (Δ g)
Δ-shift-comm (g₀ , g₁ , g₂) = refl

--------------------------------------------------------------------------------
-- §5c. 移位-卷积交换律
--------------------------------------------------------------------------------

-- 定理 5.4: 移位与卷积交换 (左)
-- S(f*g) = (Sf)*g
--
-- 代数本质: 循环卷积在循环移位下等变。
-- 证明: 三分量各用一次 ⊕-rotate₃ (三元加法循环旋转)
shift-conv-left : ∀ f g → shift (conv f g) ≡ conv (shift f) g
shift-conv-left (f₀ , f₁ , f₂) (g₀ , g₁ , g₂) =
  triple-≡
    (⊕-rotate₃ (f₀ ⊗ g₁) (f₁ ⊗ g₀) (f₂ ⊗ g₂))
    (⊕-rotate₃ (f₀ ⊗ g₂) (f₁ ⊗ g₁) (f₂ ⊗ g₀))
    (⊕-rotate₃ (f₀ ⊗ g₀) (f₁ ⊗ g₂) (f₂ ⊗ g₁))

-- 定理 5.5: 卷积交换律
-- f*g = g*f (Z/3Z 是 Abel 群, 其群代数交换)
-- 证明: ⊗-comm + 加法重排
conv-comm : ∀ f g → conv f g ≡ conv g f
conv-comm (f₀ , f₁ , f₂) (g₀ , g₁ , g₂) = triple-≡ p₀ p₁ p₂
  where
    open ≡-Reasoning
    -- 分量 0: ⊗-comm 后需 (a+b)+c = (a+c)+b
    p₀ : ((f₀ ⊗ g₀) ⊕ (f₁ ⊗ g₂)) ⊕ (f₂ ⊗ g₁) ≡
         ((g₀ ⊗ f₀) ⊕ (g₁ ⊗ f₂)) ⊕ (g₂ ⊗ f₁)
    p₀ = begin
      ((f₀ ⊗ g₀) ⊕ (f₁ ⊗ g₂)) ⊕ (f₂ ⊗ g₁)
        ≡⟨ cong (λ x → (x ⊕ (f₁ ⊗ g₂)) ⊕ (f₂ ⊗ g₁)) (⊗-comm f₀ g₀) ⟩
      ((g₀ ⊗ f₀) ⊕ (f₁ ⊗ g₂)) ⊕ (f₂ ⊗ g₁)
        ≡⟨ cong (λ x → ((g₀ ⊗ f₀) ⊕ x) ⊕ (f₂ ⊗ g₁)) (⊗-comm f₁ g₂) ⟩
      ((g₀ ⊗ f₀) ⊕ (g₂ ⊗ f₁)) ⊕ (f₂ ⊗ g₁)
        ≡⟨ cong (λ x → ((g₀ ⊗ f₀) ⊕ (g₂ ⊗ f₁)) ⊕ x) (⊗-comm f₂ g₁) ⟩
      ((g₀ ⊗ f₀) ⊕ (g₂ ⊗ f₁)) ⊕ (g₁ ⊗ f₂)
        ≡⟨ ⊕-swap-inner (g₀ ⊗ f₀) (g₂ ⊗ f₁) (g₁ ⊗ f₂) ⟩
      ((g₀ ⊗ f₀) ⊕ (g₁ ⊗ f₂)) ⊕ (g₂ ⊗ f₁)
        ∎
    -- 分量 1: ⊗-comm 后需 (a+b)+c = (b+a)+c
    p₁ : ((f₀ ⊗ g₁) ⊕ (f₁ ⊗ g₀)) ⊕ (f₂ ⊗ g₂) ≡
         ((g₀ ⊗ f₁) ⊕ (g₁ ⊗ f₀)) ⊕ (g₂ ⊗ f₂)
    p₁ = begin
      ((f₀ ⊗ g₁) ⊕ (f₁ ⊗ g₀)) ⊕ (f₂ ⊗ g₂)
        ≡⟨ cong (λ x → (x ⊕ (f₁ ⊗ g₀)) ⊕ (f₂ ⊗ g₂)) (⊗-comm f₀ g₁) ⟩
      ((g₁ ⊗ f₀) ⊕ (f₁ ⊗ g₀)) ⊕ (f₂ ⊗ g₂)
        ≡⟨ cong (λ x → ((g₁ ⊗ f₀) ⊕ x) ⊕ (f₂ ⊗ g₂)) (⊗-comm f₁ g₀) ⟩
      ((g₁ ⊗ f₀) ⊕ (g₀ ⊗ f₁)) ⊕ (f₂ ⊗ g₂)
        ≡⟨ cong (_⊕ (f₂ ⊗ g₂)) (⊕-comm (g₁ ⊗ f₀) (g₀ ⊗ f₁)) ⟩
      ((g₀ ⊗ f₁) ⊕ (g₁ ⊗ f₀)) ⊕ (f₂ ⊗ g₂)
        ≡⟨ cong (λ x → ((g₀ ⊗ f₁) ⊕ (g₁ ⊗ f₀)) ⊕ x) (⊗-comm f₂ g₂) ⟩
      ((g₀ ⊗ f₁) ⊕ (g₁ ⊗ f₀)) ⊕ (g₂ ⊗ f₂)
        ∎
    -- 分量 2: ⊗-comm 后需 (a+b)+c = (c+b)+a
    p₂ : ((f₀ ⊗ g₂) ⊕ (f₁ ⊗ g₁)) ⊕ (f₂ ⊗ g₀) ≡
         ((g₀ ⊗ f₂) ⊕ (g₁ ⊗ f₁)) ⊕ (g₂ ⊗ f₀)
    p₂ = begin
      ((f₀ ⊗ g₂) ⊕ (f₁ ⊗ g₁)) ⊕ (f₂ ⊗ g₀)
        ≡⟨ cong (λ x → (x ⊕ (f₁ ⊗ g₁)) ⊕ (f₂ ⊗ g₀)) (⊗-comm f₀ g₂) ⟩
      ((g₂ ⊗ f₀) ⊕ (f₁ ⊗ g₁)) ⊕ (f₂ ⊗ g₀)
        ≡⟨ cong (λ x → ((g₂ ⊗ f₀) ⊕ x) ⊕ (f₂ ⊗ g₀)) (⊗-comm f₁ g₁) ⟩
      ((g₂ ⊗ f₀) ⊕ (g₁ ⊗ f₁)) ⊕ (f₂ ⊗ g₀)
        ≡⟨ cong (λ x → ((g₂ ⊗ f₀) ⊕ (g₁ ⊗ f₁)) ⊕ x) (⊗-comm f₂ g₀) ⟩
      ((g₂ ⊗ f₀) ⊕ (g₁ ⊗ f₁)) ⊕ (g₀ ⊗ f₂)
        ≡⟨ cong (_⊕ (g₀ ⊗ f₂)) (⊕-comm (g₂ ⊗ f₀) (g₁ ⊗ f₁)) ⟩
      ((g₁ ⊗ f₁) ⊕ (g₂ ⊗ f₀)) ⊕ (g₀ ⊗ f₂)
        ≡⟨ ⊕-comm ((g₁ ⊗ f₁) ⊕ (g₂ ⊗ f₀)) (g₀ ⊗ f₂) ⟩
      (g₀ ⊗ f₂) ⊕ ((g₁ ⊗ f₁) ⊕ (g₂ ⊗ f₀))
        ≡⟨ sym (⊕-assoc (g₀ ⊗ f₂) (g₁ ⊗ f₁) (g₂ ⊗ f₀)) ⟩
      ((g₀ ⊗ f₂) ⊕ (g₁ ⊗ f₁)) ⊕ (g₂ ⊗ f₀)
        ∎

--------------------------------------------------------------------------------
-- §5d. 差分-卷积 Leibniz 规则 (核心定理)
--------------------------------------------------------------------------------

-- 定理 5.6: Leibniz 规则 — Δ 与卷积交换
-- Δ(f*g) = f*(Δg)
--
-- 证明策略:
--   1. conv f g = f₀·g + f₁·S²g + f₂·Sg  (conv-decomp)
--   2. Δ 保持加法 (Δ-linear)
--   3. Δ 与标量乘法交换 (Δ-scalar-comm)
--   4. Δ 与移位交换 (Δ-shift-comm, 定义归约)
--   5. 重组为 conv f (Δg) (sym conv-decomp)
--
-- 数学意义:
--   差分算子 Δ 是卷积代数 (GF3Func, *, +) 的导子。
--   这是离散微积分基本定理: 微分与卷积交换。
--   在信号处理中, 这意味着 LTI 系统的微分等于输入的微分通过系统。
Δ-conv-leibniz : ∀ f g → Δ (conv f g) ≡ conv f (Δ g)
Δ-conv-leibniz (f₀ , f₁ , f₂) (g₀ , g₁ , g₂) = begin
  Δ (conv (f₀ , f₁ , f₂) (g₀ , g₁ , g₂))
    ≡⟨ cong Δ (conv-decomp f₀ f₁ f₂ g₀ g₁ g₂) ⟩
  Δ ((f₀ ⊗f (g₀ , g₁ , g₂)) ⊕f (f₁ ⊗f (g₂ , g₀ , g₁)) ⊕f (f₂ ⊗f (g₁ , g₂ , g₀)))
    ≡⟨ Δ-linear ((f₀ ⊗f (g₀ , g₁ , g₂)) ⊕f (f₁ ⊗f (g₂ , g₀ , g₁)))
                (f₂ ⊗f (g₁ , g₂ , g₀)) ⟩
  Δ ((f₀ ⊗f (g₀ , g₁ , g₂)) ⊕f (f₁ ⊗f (g₂ , g₀ , g₁)))
    ⊕f Δ (f₂ ⊗f (g₁ , g₂ , g₀))
    ≡⟨ cong (_⊕f Δ (f₂ ⊗f (g₁ , g₂ , g₀)))
            (Δ-linear (f₀ ⊗f (g₀ , g₁ , g₂)) (f₁ ⊗f (g₂ , g₀ , g₁))) ⟩
  (Δ (f₀ ⊗f (g₀ , g₁ , g₂)) ⊕f Δ (f₁ ⊗f (g₂ , g₀ , g₁)))
    ⊕f Δ (f₂ ⊗f (g₁ , g₂ , g₀))
    ≡⟨ cong (λ x → (x ⊕f Δ (f₁ ⊗f (g₂ , g₀ , g₁)))
                    ⊕f Δ (f₂ ⊗f (g₁ , g₂ , g₀)))
            (Δ-scalar-comm f₀ (g₀ , g₁ , g₂)) ⟩
  ((f₀ ⊗f Δ (g₀ , g₁ , g₂)) ⊕f Δ (f₁ ⊗f (g₂ , g₀ , g₁)))
    ⊕f Δ (f₂ ⊗f (g₁ , g₂ , g₀))
    ≡⟨ cong (λ x → ((f₀ ⊗f Δ (g₀ , g₁ , g₂)) ⊕f x)
                    ⊕f Δ (f₂ ⊗f (g₁ , g₂ , g₀)))
            (Δ-scalar-comm f₁ (g₂ , g₀ , g₁)) ⟩
  ((f₀ ⊗f Δ (g₀ , g₁ , g₂)) ⊕f (f₁ ⊗f Δ (g₂ , g₀ , g₁)))
    ⊕f Δ (f₂ ⊗f (g₁ , g₂ , g₀))
    ≡⟨ cong (λ x → ((f₀ ⊗f Δ (g₀ , g₁ , g₂)) ⊕f (f₁ ⊗f Δ (g₂ , g₀ , g₁)))
                    ⊕f x)
            (Δ-scalar-comm f₂ (g₁ , g₂ , g₀)) ⟩
  ((f₀ ⊗f Δ (g₀ , g₁ , g₂)) ⊕f (f₁ ⊗f Δ (g₂ , g₀ , g₁)))
    ⊕f (f₂ ⊗f Δ (g₁ , g₂ , g₀))
    ≡⟨ sym (conv-decomp f₀ f₁ f₂
             (g₁ ⊕ negate g₀) (g₂ ⊕ negate g₁) (g₀ ⊕ negate g₂)) ⟩
  conv (f₀ , f₁ , f₂) (Δ (g₀ , g₁ , g₂))
  ∎
  where open ≡-Reasoning

-- 定理 5.7: Leibniz 规则 (右形式)
-- Δ(f*g) = (Δf)*g
-- 证明: f*g = g*f → Δ(g*f) = g*(Δf) → (Δf)*g
Δ-conv-leibniz' : ∀ f g → Δ (conv f g) ≡ conv (Δ f) g
Δ-conv-leibniz' f g = begin
  Δ (conv f g)
    ≡⟨ cong Δ (conv-comm f g) ⟩
  Δ (conv g f)
    ≡⟨ Δ-conv-leibniz g f ⟩
  conv g (Δ f)
    ≡⟨ conv-comm g (Δ f) ⟩
  conv (Δ f) g
  ∎
  where open ≡-Reasoning

-- 定理 5.8: 二阶 Leibniz 规则
-- Δ²(f*g) = f*(Δ²g)
-- 证明: 两次应用定理 5.6
Δ²-conv-leibniz : ∀ f g → Δ (Δ (conv f g)) ≡ conv f (Δ (Δ g))
Δ²-conv-leibniz f g = begin
  Δ (Δ (conv f g))
    ≡⟨ cong Δ (Δ-conv-leibniz f g) ⟩
  Δ (conv f (Δ g))
    ≡⟨ Δ-conv-leibniz f (Δ g) ⟩
  conv f (Δ (Δ g))
  ∎
  where open ≡-Reasoning

-- 定理 5.9: 三阶 Leibniz 规则 → 零
-- Δ³(f*g) = f*(Δ³g) = f*0 = 0
-- 这是 §1 同调截断在卷积代数中的表现:
-- 卷积不创造新的同调信息 — 三阶以上同调在卷积下仍然消失。
Δ³-conv-zero : ∀ f g → Δ (Δ (Δ (conv f g))) ≡ (T₀ , T₀ , T₀)
Δ³-conv-zero f g = Δ³≡0 (conv f g)

--------------------------------------------------------------------------------
-- 总结
--
-- §1. 同调截断:
--   Δ³≡0 → im(Δ³) = {0} → 三阶以上同调消失
--   ker(Δ) = 常数函数 (H⁰ 的离散模拟)
--   Δⁿ≡0 对所有 n ≥ 3 (幂零性推广)
--
-- §2. Euler 示性数:
--   χ(T⁶) = Σ(-1)^k C(6,k) = 32 - 32 = 0
--   Betti 数总和 = 2⁶ = 64
--
-- §3. Plancherel (A₄):
--   特征标正交性: ⟨χ_ρ, χ_σ⟩ = 12·δ_{ρσ}
--   维数公式: Σ dim(ρ)² = 12 = |A₄|
--   全部通过 Z[ω] 穷举计算验证
--
-- §4. 卷积定理 (Z/3Z) — DC 分量:
--   sum3(f*g) = sum3(f) · sum3(g) (增广同态)
--   δ 是卷积单位元
--   证明: 分解 → 线性 → 移位不变 → 分配律
--
-- §5. 差分-卷积 Leibniz 规则 — 非 DC 分量:
--   S(f*g) = (Sf)*g (移位-卷积交换)
--   Δ(f*g) = f*(Δg) = (Δf)*g (Leibniz 规则)
--   Δ²(f*g) = f*(Δ²g) (二阶推广)
--   Δ³(f*g) = 0 (同调截断在卷积下封闭)
--   GF(3) 无本原三次单位根 → DFT 卷积定理退化 → Leibniz 规则是正确替代
--------------------------------------------------------------------------------
