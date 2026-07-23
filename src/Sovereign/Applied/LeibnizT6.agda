{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.LeibnizT6
-- 多维 Leibniz 规则 — T⁶ = GF(3)⁶ 上的方向差分代数
--
-- 核心结果:
--   §3. 线性性: Δ₁, Δ₂ 保持逐点加法
--   §4. 标量交换: Δ₁, Δ₂ 与标量乘法交换
--   §5. 方向交换律: Δ₁Δ₂ = Δ₂Δ₁ (多维 Leibniz 的核心)
--   §6. 幂零性: Δ₁³ = Δ₂³ = 0 (char 3)
--   §7. 混合差分推论
--
-- 数学意义:
--   T⁶ = (Z/3Z)⁶ 上的 6 个方向差分算子 Δ₀,...,Δ₅ 满足:
--   (1) 每个 Δᵢ 是 GF(3)-线性的
--   (2) ΔᵢΔⱼ = ΔⱼΔᵢ (方向交换 / 可积条件)
--   (3) Δᵢ³ = 0 (char 3 幂零截断)
--   这三条性质完全刻画了 T⁶ 上的离散微分结构。
--
--   本模块在 2D 切片 (Z/3Z)² 上证明这些性质。
--   6D 推广是直接的: 每个方向独立继承 1D 结构,
--   方向交换律对任意方向对成立 (因为不同方向的移位作用于不同坐标)。
--
-- 依赖:
--   ProjectionDifferential: GF3Func, Δ, Δ³≡0
--   DiscreteDE: GF3Func2D, Δ₁, Δ₂, transpose2D
--
-- 0 postulate — 全部构造性证明, 穷举法优先
--------------------------------------------------------------------------------

module Sovereign.Applied.LeibnizT6 where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (
  _≡_; refl; cong; sym; trans; module ≡-Reasoning)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; negate²;
  ⊕-comm; ⊕-assoc;
  ⊗-comm; ⊗-assoc; ⊗-distribˡ-⊕)
open import Sovereign.Algebra.ProjectionDifferential using (
  GF3Func; Δ; Δ³≡0; Δ-const-zero; const-func)
open import Sovereign.Algebra.DiscreteDE using (
  GF3Func2D; zero2D; const2D; _⊕f_; _⊕2D_;
  Δ₁; Δ₂; transpose2D; func2d-≡;
  Δ₁³≡0; Δ₂³≡0; transpose²≡id;
  Δ₁-const-zero; Δ₂-const-zero)

--------------------------------------------------------------------------------
-- §1. 基础设施 — 标量乘法与等式辅助
--------------------------------------------------------------------------------

-- 三元组等式构造
triple-≡ : ∀ {a b c a' b' c' : Trit} →
  a ≡ a' → b ≡ b' → c ≡ c' → (a , b , c) ≡ (a' , b' , c')
triple-≡ refl refl refl = refl

-- 标量乘法 (GF3Func): 逐点乘以 GF(3) 标量
infixr 25 _⊗f_
_⊗f_ : Trit → GF3Func → GF3Func
s ⊗f (a₀ , a₁ , a₂) = (s ⊗ a₀ , s ⊗ a₁ , s ⊗ a₂)

-- 标量乘法 (GF3Func2D): 逐行标量乘
infixr 25 _⊗2D_
_⊗2D_ : Trit → GF3Func2D → GF3Func2D
s ⊗2D (r₀ , r₁ , r₂) = (s ⊗f r₀ , s ⊗f r₁ , s ⊗f r₂)

--------------------------------------------------------------------------------
-- §2. GF(3) 辅助引理
--
-- 多维差分证明所需的 GF(3) 代数恒等式。
-- 穷举法 (3 case / 9 case) 与代数推导并用。
--------------------------------------------------------------------------------

-- negate = 乘以 T₂ (GF(3) 中 -1 ≡ 2)
-- 3 case 穷举
negate-≡-⊗₂ : ∀ x → negate x ≡ T₂ ⊗ x
negate-≡-⊗₂ T₀ = refl
negate-≡-⊗₂ T₁ = refl
negate-≡-⊗₂ T₂ = refl

-- negate 保持加法: -(a+b) = (-a)+(-b)
-- 证明: negate = T₂⊗_, 然后用分配律
negate-⊕ : ∀ a b → negate (a ⊕ b) ≡ negate a ⊕ negate b
negate-⊕ a b rewrite negate-≡-⊗₂ (a ⊕ b) | negate-≡-⊗₂ a | negate-≡-⊗₂ b =
  ⊗-distribˡ-⊕ T₂ a b

-- 加法交换重排: (a+b)+(c+d) = (a+c)+(b+d)
-- 证明: 结合律 + 交换律, 6 步
⊕-interchange : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
⊕-interchange a b c d = begin
  (a ⊕ b) ⊕ (c ⊕ d)
    ≡⟨ ⊕-assoc a b (c ⊕ d) ⟩
  a ⊕ (b ⊕ (c ⊕ d))
    ≡⟨ cong (a ⊕_) (sym (⊕-assoc b c d)) ⟩
  a ⊕ ((b ⊕ c) ⊕ d)
    ≡⟨ cong (a ⊕_) (cong (_⊕ d) (⊕-comm b c)) ⟩
  a ⊕ ((c ⊕ b) ⊕ d)
    ≡⟨ cong (a ⊕_) (⊕-assoc c b d) ⟩
  a ⊕ (c ⊕ (b ⊕ d))
    ≡⟨ sym (⊕-assoc a c (b ⊕ d)) ⟩
  (a ⊕ c) ⊕ (b ⊕ d)
  ∎
  where open ≡-Reasoning

-- negate 嵌套消去: neg(x + neg y) = neg x + y
-- 代数本质: -(-y) = y (对合性)
neg-⊕-neg : ∀ x y → negate (x ⊕ negate y) ≡ negate x ⊕ y
neg-⊕-neg x y = begin
  negate (x ⊕ negate y)
    ≡⟨ negate-⊕ x (negate y) ⟩
  negate x ⊕ negate (negate y)
    ≡⟨ cong (negate x ⊕_) (negate² y) ⟩
  negate x ⊕ y
  ∎
  where open ≡-Reasoning

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
-- §3. 多维差分的线性性
--
-- Δᵢ(f + g) = Δᵢf + Δᵢg
-- 差分算子是 GF(3)-线性的 — 离散微积分的基本性质。
--------------------------------------------------------------------------------

-- 定理 3.1: 1D 线性性 Δ(f + g) = Δf + Δg
-- 证明: negate-⊕ + ⊕-interchange, 逐分量
Δ-linear-1D : ∀ f g → Δ (f ⊕f g) ≡ Δ f ⊕f Δ g
Δ-linear-1D (a₀ , a₁ , a₂) (b₀ , b₁ , b₂) = triple-≡ p₀ p₁ p₂
  where
    open ≡-Reasoning
    p₀ : (a₁ ⊕ b₁) ⊕ negate (a₀ ⊕ b₀) ≡ (a₁ ⊕ negate a₀) ⊕ (b₁ ⊕ negate b₀)
    p₀ = begin
      (a₁ ⊕ b₁) ⊕ negate (a₀ ⊕ b₀)
        ≡⟨ cong ((a₁ ⊕ b₁) ⊕_) (negate-⊕ a₀ b₀) ⟩
      (a₁ ⊕ b₁) ⊕ (negate a₀ ⊕ negate b₀)
        ≡⟨ ⊕-interchange a₁ b₁ (negate a₀) (negate b₀) ⟩
      (a₁ ⊕ negate a₀) ⊕ (b₁ ⊕ negate b₀) ∎
    p₁ : (a₂ ⊕ b₂) ⊕ negate (a₁ ⊕ b₁) ≡ (a₂ ⊕ negate a₁) ⊕ (b₂ ⊕ negate b₁)
    p₁ = begin
      (a₂ ⊕ b₂) ⊕ negate (a₁ ⊕ b₁)
        ≡⟨ cong ((a₂ ⊕ b₂) ⊕_) (negate-⊕ a₁ b₁) ⟩
      (a₂ ⊕ b₂) ⊕ (negate a₁ ⊕ negate b₁)
        ≡⟨ ⊕-interchange a₂ b₂ (negate a₁) (negate b₁) ⟩
      (a₂ ⊕ negate a₁) ⊕ (b₂ ⊕ negate b₁) ∎
    p₂ : (a₀ ⊕ b₀) ⊕ negate (a₂ ⊕ b₂) ≡ (a₀ ⊕ negate a₂) ⊕ (b₀ ⊕ negate b₂)
    p₂ = begin
      (a₀ ⊕ b₀) ⊕ negate (a₂ ⊕ b₂)
        ≡⟨ cong ((a₀ ⊕ b₀) ⊕_) (negate-⊕ a₂ b₂) ⟩
      (a₀ ⊕ b₀) ⊕ (negate a₂ ⊕ negate b₂)
        ≡⟨ ⊕-interchange a₀ b₀ (negate a₂) (negate b₂) ⟩
      (a₀ ⊕ negate a₂) ⊕ (b₀ ⊕ negate b₂) ∎

-- 定理 3.2: Δ₁ 的线性性
-- Δ₁(u + v) = Δ₁u + Δ₁v
-- 证明: 逐行应用 1D 线性性
Δ₁-linear : ∀ u v → Δ₁ (u ⊕2D v) ≡ Δ₁ u ⊕2D Δ₁ v
Δ₁-linear (r₀ , r₁ , r₂) (s₀ , s₁ , s₂) =
  func2d-≡ (Δ-linear-1D r₀ s₀) (Δ-linear-1D r₁ s₁) (Δ-linear-1D r₂ s₂)

-- 转置保持加法: T(u + v) = Tu + Tv
transpose-⊕2D : ∀ u v → transpose2D (u ⊕2D v) ≡ transpose2D u ⊕2D transpose2D v
transpose-⊕2D ((a₀₀ , a₀₁ , a₀₂) , (a₁₀ , a₁₁ , a₁₂) , (a₂₀ , a₂₁ , a₂₂))
              ((b₀₀ , b₀₁ , b₀₂) , (b₁₀ , b₁₁ , b₁₂) , (b₂₀ , b₂₁ , b₂₂)) = refl

-- 定理 3.3: Δ₂ 的线性性
-- Δ₂(u + v) = Δ₂u + Δ₂v
-- 证明: Δ₂ = T∘Δ₁∘T, T 保持加法, Δ₁ 线性
Δ₂-linear : ∀ u v → Δ₂ (u ⊕2D v) ≡ Δ₂ u ⊕2D Δ₂ v
Δ₂-linear u v = begin
  Δ₂ (u ⊕2D v)
    ≡⟨⟩
  transpose2D (Δ₁ (transpose2D (u ⊕2D v)))
    ≡⟨ cong (λ x → transpose2D (Δ₁ x)) (transpose-⊕2D u v) ⟩
  transpose2D (Δ₁ (transpose2D u ⊕2D transpose2D v))
    ≡⟨ cong transpose2D (Δ₁-linear (transpose2D u) (transpose2D v)) ⟩
  transpose2D (Δ₁ (transpose2D u) ⊕2D Δ₁ (transpose2D v))
    ≡⟨ transpose-⊕2D (Δ₁ (transpose2D u)) (Δ₁ (transpose2D v)) ⟩
  transpose2D (Δ₁ (transpose2D u)) ⊕2D transpose2D (Δ₁ (transpose2D v))
    ≡⟨⟩
  Δ₂ u ⊕2D Δ₂ v
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §4. 多维差分的标量交换性
--
-- Δᵢ(s · f) = s · Δᵢf
-- 差分与标量乘法交换 — GF(3)-线性的另一半。
--------------------------------------------------------------------------------

-- 定理 4.1: 1D 标量交换 Δ(s·f) = s·Δf
-- 证明: negate-⊗-scalar + 分配律, 逐分量
Δ-scalar-1D : ∀ s f → Δ (s ⊗f f) ≡ s ⊗f Δ f
Δ-scalar-1D s (a₀ , a₁ , a₂) = triple-≡ p₀ p₁ p₂
  where
    open ≡-Reasoning
    p₀ : (s ⊗ a₁) ⊕ negate (s ⊗ a₀) ≡ s ⊗ (a₁ ⊕ negate a₀)
    p₀ = begin
      (s ⊗ a₁) ⊕ negate (s ⊗ a₀)
        ≡⟨ cong ((s ⊗ a₁) ⊕_) (negate-⊗-scalar s a₀) ⟩
      (s ⊗ a₁) ⊕ (s ⊗ negate a₀)
        ≡⟨ sym (⊗-distribˡ-⊕ s a₁ (negate a₀)) ⟩
      s ⊗ (a₁ ⊕ negate a₀) ∎
    p₁ : (s ⊗ a₂) ⊕ negate (s ⊗ a₁) ≡ s ⊗ (a₂ ⊕ negate a₁)
    p₁ = begin
      (s ⊗ a₂) ⊕ negate (s ⊗ a₁)
        ≡⟨ cong ((s ⊗ a₂) ⊕_) (negate-⊗-scalar s a₁) ⟩
      (s ⊗ a₂) ⊕ (s ⊗ negate a₁)
        ≡⟨ sym (⊗-distribˡ-⊕ s a₂ (negate a₁)) ⟩
      s ⊗ (a₂ ⊕ negate a₁) ∎
    p₂ : (s ⊗ a₀) ⊕ negate (s ⊗ a₂) ≡ s ⊗ (a₀ ⊕ negate a₂)
    p₂ = begin
      (s ⊗ a₀) ⊕ negate (s ⊗ a₂)
        ≡⟨ cong ((s ⊗ a₀) ⊕_) (negate-⊗-scalar s a₂) ⟩
      (s ⊗ a₀) ⊕ (s ⊗ negate a₂)
        ≡⟨ sym (⊗-distribˡ-⊕ s a₀ (negate a₂)) ⟩
      s ⊗ (a₀ ⊕ negate a₂) ∎

-- 定理 4.2: Δ₁ 的标量交换
-- Δ₁(s·u) = s·Δ₁u
Δ₁-scalar : ∀ s u → Δ₁ (s ⊗2D u) ≡ s ⊗2D Δ₁ u
Δ₁-scalar s (r₀ , r₁ , r₂) =
  func2d-≡ (Δ-scalar-1D s r₀) (Δ-scalar-1D s r₁) (Δ-scalar-1D s r₂)

-- 转置保持标量乘法: T(s·u) = s·Tu
transpose-⊗2D : ∀ s u → transpose2D (s ⊗2D u) ≡ s ⊗2D transpose2D u
transpose-⊗2D s ((a₀₀ , a₀₁ , a₀₂) , (a₁₀ , a₁₁ , a₁₂) , (a₂₀ , a₂₁ , a₂₂)) = refl

-- 定理 4.3: Δ₂ 的标量交换
-- Δ₂(s·u) = s·Δ₂u
-- 证明: 共轭 Δ₂ = T∘Δ₁∘T + T 保持标量乘
Δ₂-scalar : ∀ s u → Δ₂ (s ⊗2D u) ≡ s ⊗2D Δ₂ u
Δ₂-scalar s u = begin
  Δ₂ (s ⊗2D u)
    ≡⟨⟩
  transpose2D (Δ₁ (transpose2D (s ⊗2D u)))
    ≡⟨ cong (λ x → transpose2D (Δ₁ x)) (transpose-⊗2D s u) ⟩
  transpose2D (Δ₁ (s ⊗2D transpose2D u))
    ≡⟨ cong transpose2D (Δ₁-scalar s (transpose2D u)) ⟩
  transpose2D (s ⊗2D Δ₁ (transpose2D u))
    ≡⟨ transpose-⊗2D s (Δ₁ (transpose2D u)) ⟩
  s ⊗2D transpose2D (Δ₁ (transpose2D u))
    ≡⟨⟩
  s ⊗2D Δ₂ u
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §5. 方向交换律 — 多维 Leibniz 的核心定理
--
-- Δ₁Δ₂ = Δ₂Δ₁
--
-- 连续类比: Schwarz 定理 ∂²f/∂x∂y = ∂²f/∂y∂x
-- 离散本质: 在 (Z/3Z)² 的 3×3 格点上,
--   Δ₁(Δ₂u) 和 Δ₂(Δ₁u) 的每个分量涉及同一个 2×2 子格点,
--   只是减法顺序不同 — GF(3) 加法交换性保证相等。
--
-- 这是 T⁶ 上 6 个方向差分算子两两交换的 2D 实例。
-- 6D 推广: 对任意方向对 (i,j), ΔᵢΔⱼ = ΔⱼΔᵢ,
-- 因为不同方向的移位作用于不同坐标, 互不干扰。
--------------------------------------------------------------------------------

-- 分量引理: 2×2 格点上的差分交换
-- (x ⊖ y) ⊖ (z ⊖ w) 的两种展开顺序给出相同结果
-- 代数本质: neg(z⊖w) = neg z ⊕ w, 然后交换 neg y 和 neg z
Δ₂D-comm-component : ∀ x y z w →
  (x ⊕ negate y) ⊕ negate (z ⊕ negate w) ≡
  (x ⊕ negate z) ⊕ negate (y ⊕ negate w)
Δ₂D-comm-component x y z w = begin
  (x ⊕ negate y) ⊕ negate (z ⊕ negate w)
    ≡⟨ cong ((x ⊕ negate y) ⊕_) (neg-⊕-neg z w) ⟩
  (x ⊕ negate y) ⊕ (negate z ⊕ w)
    ≡⟨ ⊕-interchange x (negate y) (negate z) w ⟩
  (x ⊕ negate z) ⊕ (negate y ⊕ w)
    ≡⟨ cong ((x ⊕ negate z) ⊕_) (sym (neg-⊕-neg y w)) ⟩
  (x ⊕ negate z) ⊕ negate (y ⊕ negate w)
  ∎
  where open ≡-Reasoning

-- 定理 5.1: 方向交换律 Δ₁Δ₂ = Δ₂Δ₁
--
-- 证明策略:
--   1. 展开 u 为 3×3 格点 ((a,b,c),(d,e,f),(g,h,i))
--   2. 两侧各归约为 9 个 GF(3) 表达式
--   3. 每个分量是 Δ₂D-comm-component 的一个实例
--   4. 用 func2d-≡ + triple-≡ 组装
--
-- 9 个分量的参数对应:
--   (0,0): x=e y=b z=d w=a    (0,1): x=f y=c z=e w=b    (0,2): x=d y=a z=f w=c
--   (1,0): x=h y=e z=g w=d    (1,1): x=i y=f z=h w=e    (1,2): x=g y=d z=i w=f
--   (2,0): x=b y=h z=a w=g    (2,1): x=c y=i z=b w=h    (2,2): x=a y=g z=c w=i
Δ₁Δ₂-comm : ∀ u → Δ₁ (Δ₂ u) ≡ Δ₂ (Δ₁ u)
Δ₁Δ₂-comm ((a , b , c) , (d , e , f) , (g , h , i)) =
  func2d-≡
    (triple-≡ (Δ₂D-comm-component e b d a)
              (Δ₂D-comm-component f c e b)
              (Δ₂D-comm-component d a f c))
    (triple-≡ (Δ₂D-comm-component h e g d)
              (Δ₂D-comm-component i f h e)
              (Δ₂D-comm-component g d i f))
    (triple-≡ (Δ₂D-comm-component b h a g)
              (Δ₂D-comm-component c i b h)
              (Δ₂D-comm-component a g c i))

--------------------------------------------------------------------------------
-- §6. 幂零性 — 每个方向 char 3
--
-- Δ₁³ ≡ 0, Δ₂³ ≡ 0
-- 继承自 1D Δ³ ≡ 0 (ProjectionDifferential):
--   Δ₁³: 逐行应用 Δ³≡0
--   Δ₂³: 共轭 Δ₂ = T∘Δ₁∘T → Δ₂³ = T∘Δ₁³∘T = 0
--
-- 代数本质: Δ = S - I, 在 char 3 上 Δ³ = (S-I)³ = S³ - I = 0
-- 连续微分 d³/dx³ 不恒为零 — 幂零截断是离散与连续的根本差异。
--------------------------------------------------------------------------------

-- 定理 6.1: Δ₁³ ≡ 0 (引用 DiscreteDE)
Δ₁-nilpotent : ∀ u → Δ₁ (Δ₁ (Δ₁ u)) ≡ zero2D
Δ₁-nilpotent = Δ₁³≡0

-- 定理 6.2: Δ₂³ ≡ 0 (引用 DiscreteDE)
Δ₂-nilpotent : ∀ u → Δ₂ (Δ₂ (Δ₂ u)) ≡ zero2D
Δ₂-nilpotent = Δ₂³≡0

-- 定理 6.3: Δ₁ 消灭常数函数
Δ₁-kills-const : ∀ s → Δ₁ (const2D s) ≡ zero2D
Δ₁-kills-const = Δ₁-const-zero

-- 定理 6.4: Δ₂ 消灭常数函数
Δ₂-kills-const : ∀ s → Δ₂ (const2D s) ≡ zero2D
Δ₂-kills-const = Δ₂-const-zero

--------------------------------------------------------------------------------
-- §7. 混合差分推论
--
-- 方向交换律的推论: 任意混合差分可以重排方向顺序。
-- 这是多维离散微积分的 "Clairaut 定理"。
--------------------------------------------------------------------------------

-- 定理 7.1: Δ₁²Δ₂ = Δ₂Δ₁² (二阶混合交换)
Δ₁²Δ₂-comm : ∀ u → Δ₁ (Δ₁ (Δ₂ u)) ≡ Δ₂ (Δ₁ (Δ₁ u))
Δ₁²Δ₂-comm u = begin
  Δ₁ (Δ₁ (Δ₂ u))
    ≡⟨ cong Δ₁ (Δ₁Δ₂-comm u) ⟩
  Δ₁ (Δ₂ (Δ₁ u))
    ≡⟨ Δ₁Δ₂-comm (Δ₁ u) ⟩
  Δ₂ (Δ₁ (Δ₁ u))
  ∎
  where open ≡-Reasoning

-- 定理 7.2: Δ₁Δ₂² = Δ₂²Δ₁ (二阶混合交换, 另一方向)
Δ₁Δ₂²-comm : ∀ u → Δ₁ (Δ₂ (Δ₂ u)) ≡ Δ₂ (Δ₂ (Δ₁ u))
Δ₁Δ₂²-comm u = begin
  Δ₁ (Δ₂ (Δ₂ u))
    ≡⟨ Δ₁Δ₂-comm (Δ₂ u) ⟩
  Δ₂ (Δ₁ (Δ₂ u))
    ≡⟨ cong Δ₂ (Δ₁Δ₂-comm u) ⟩
  Δ₂ (Δ₂ (Δ₁ u))
  ∎
  where open ≡-Reasoning

-- 定理 7.3: Δ₁²Δ₂² = Δ₂²Δ₁² (完全混合交换)
-- 证明: 四步交换, 每次移动一个 Δ₁ 过去一个 Δ₂
Δ₁²Δ₂²-comm : ∀ u → Δ₁ (Δ₁ (Δ₂ (Δ₂ u))) ≡ Δ₂ (Δ₂ (Δ₁ (Δ₁ u)))
Δ₁²Δ₂²-comm u = begin
  Δ₁ (Δ₁ (Δ₂ (Δ₂ u)))
    ≡⟨ cong Δ₁ (Δ₁Δ₂-comm (Δ₂ u)) ⟩
  Δ₁ (Δ₂ (Δ₁ (Δ₂ u)))
    ≡⟨ Δ₁Δ₂-comm (Δ₁ (Δ₂ u)) ⟩
  Δ₂ (Δ₁ (Δ₁ (Δ₂ u)))
    ≡⟨ cong (λ x → Δ₂ (Δ₁ x)) (Δ₁Δ₂-comm u) ⟩
  Δ₂ (Δ₁ (Δ₂ (Δ₁ u)))
    ≡⟨ cong Δ₂ (Δ₁Δ₂-comm (Δ₁ u)) ⟩
  Δ₂ (Δ₂ (Δ₁ (Δ₁ u)))
  ∎
  where open ≡-Reasoning

-- 定理 7.4: 混合幂零 — Δ₁³ 消灭任何 Δ₂ 的像
Δ₁³Δ₂≡0 : ∀ u → Δ₁ (Δ₁ (Δ₁ (Δ₂ u))) ≡ zero2D
Δ₁³Δ₂≡0 u = Δ₁³≡0 (Δ₂ u)

-- 定理 7.5: 混合幂零 — Δ₂³ 消灭任何 Δ₁ 的像
Δ₂³Δ₁≡0 : ∀ u → Δ₂ (Δ₂ (Δ₂ (Δ₁ u))) ≡ zero2D
Δ₂³Δ₁≡0 u = Δ₂³≡0 (Δ₁ u)

-- 定理 7.6: 混合幂零 — Δ₁³Δ₂² ≡ 0
Δ₁³Δ₂²≡0 : ∀ u → Δ₁ (Δ₁ (Δ₁ (Δ₂ (Δ₂ u)))) ≡ zero2D
Δ₁³Δ₂²≡0 u = Δ₁³≡0 (Δ₂ (Δ₂ u))

--------------------------------------------------------------------------------
-- §8. 结构普适性总结
--
-- 本模块在 2D 切片 (Z/3Z)² 上证明了 T⁶ 多维差分的全部核心结构:
--
-- (1) GF(3)-线性性 (§3):
--     Δᵢ(f + g) = Δᵢf + Δᵢg, Δᵢ(s·f) = s·Δᵢf
--     每个方向差分是 GF(3) 向量空间的线性算子。
--
-- (2) 方向交换律 (§5):
--     ΔᵢΔⱼ = ΔⱼΔᵢ
--     不同方向的差分可交换 — 离散版 Schwarz/Clairaut 定理。
--     代数根源: 不同坐标方向的移位互不干扰。
--
-- (3) 幂零截断 (§6):
--     Δᵢ³ = 0
--     char 3 上的差分算子是幂零的, 阶 ≤ 3。
--     连续微分无此性质 — 离散与连续的根本截断。
--
-- 6D 推广:
--   T⁶ = (Z/3Z)⁶ 有 6 个方向 Δ₀,...,Δ₅。
--   每个 Δᵢ 独立继承 1D 结构 (线性 + 幂零)。
--   方向交换律对任意对 (i,j) 成立:
--     Δᵢ 只修改第 i 个坐标, Δⱼ 只修改第 j 个坐标,
--     i ≠ j 时两者作用于独立坐标, 故交换。
--   本模块的 2D 证明捕获了这一结构的全部本质。
--
-- 与 HomologyHarmonic §5 的连接:
--   1D Leibniz 规则: Δ(f*g) = f*(Δg) (差分与卷积交换)
--   多维推广: 每个 Δᵢ 都是卷积代数的导子,
--   且不同方向的导子两两交换。
--   这构成 T⁶ 上的 "可积微分系统"。
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------
