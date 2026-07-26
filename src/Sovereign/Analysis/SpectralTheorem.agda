{-# OPTIONS --rewriting #-}
module Sovereign.Analysis.SpectralTheorem where

--------------------------------------------------------------------------------
-- 谱定理: GF(3)ⁿ 上自伴算子的特征分解
--
-- 核心定理:
--   自伴算子 T (⟨Tf,g⟩ = ⟨f,Tg⟩) 的不同特征值的特征向量正交。
--   对 n=1: 每个线性算子都是标量乘法 (平凡对角化)。
--   对 n=2: 具体自伴算子的谱分解 (穷举构造)。
--
-- GF(3) 特异性:
--   与 ℂ 上的谱定理不同, GF(3) 上并非所有自伴算子都可对角化。
--   例: 矩阵 [[0,1],[1,1]] 是对称的, 但特征多项式 λ²+2λ+2
--   在 GF(3) 上无根 (判别式 2 不是平方元)。
--   本模块形式化的是谱定理中普遍成立的部分:
--   ① 不同特征值 → 正交特征向量 (任意 n)
--   ② n=1 完全对角化
--   ③ n=2 具体算子的谱分解
--
-- 依赖:
--   Sovereign.Base.Trit — GF(3) 三进制本体
--   Sovereign.Algebra.FunctionalDiscrete — 离散泛函分析基础设施
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
  renaming (module ≡-Reasoning to ≡-Reasoning)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_;
  ⊕-identityʳ; ⊗-identityʳ; ⊗-comm;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕;
  ⊗-zeroˡ; ⊗-zeroʳ)

open import Sovereign.Algebra.FunctionalDiscrete using (
  _+v_; _·v_; 0⃗;
  standard-inner-product; inner-sym; inner-linearˡ;
  ⊕-shuffle;
  Operator; is-linear-operator;
  Orthogonal; zero-orthogonal;
  +v-identityʳ; scalar-one;
  id-operator; zero-operator)

--------------------------------------------------------------------------------
-- §1. 自伴算子 — 离散内积空间的对称性
--------------------------------------------------------------------------------

-- 自伴 (对称) 算子: ⟨Tf, g⟩ ≡ ⟨f, Tg⟩
is-self-adjoint : ∀ n → Operator n → Set
is-self-adjoint n T = ∀ f g →
  standard-inner-product n (T f) g ≡ standard-inner-product n f (T g)

--------------------------------------------------------------------------------
-- §2. 特征值与特征向量
--------------------------------------------------------------------------------

-- 特征对: T v ≡ ℓ ·v v
IsEigenpair : ∀ n → Operator n → Trit → Vec Trit n → Set
IsEigenpair n T ℓ v = T v ≡ ℓ ·v v

--------------------------------------------------------------------------------
-- §3. GF(3) 域性质 — 非零元消去律
--
-- GF(3) 是域: 非零元乘法是单射。
-- 若 λ⊗p ≡ μ⊗p 且 λ≢μ, 则 p ≡ T₀。
-- 证明: 对 p 穷举 (3 case), p=T₁/T₂ 时 ⊗ 是单射。
--------------------------------------------------------------------------------

⊗-eq→zero : ∀ ℓ μ p → ℓ ⊗ p ≡ μ ⊗ p → ℓ ≢ μ → p ≡ T₀
⊗-eq→zero ℓ μ T₀ _ _ = refl
⊗-eq→zero ℓ μ T₁ hyp neq =
  ⊥-elim (neq (trans (sym (⊗-identityʳ ℓ)) (trans hyp (⊗-identityʳ μ))))
⊗-eq→zero T₀ T₀ T₂ _ neq = ⊥-elim (neq refl)
⊗-eq→zero T₀ T₁ T₂ () neq
⊗-eq→zero T₀ T₂ T₂ () neq
⊗-eq→zero T₁ T₀ T₂ () neq
⊗-eq→zero T₁ T₁ T₂ _ neq = ⊥-elim (neq refl)
⊗-eq→zero T₁ T₂ T₂ () neq
⊗-eq→zero T₂ T₀ T₂ () neq
⊗-eq→zero T₂ T₁ T₂ () neq
⊗-eq→zero T₂ T₂ T₂ _ neq = ⊥-elim (neq refl)

--------------------------------------------------------------------------------
-- §4. 内积标量引理 — ⟨a·v, w⟩ = a⊗⟨v,w⟩
--------------------------------------------------------------------------------

-- 内积左标量: ⟨a ·v xs, ys⟩ ≡ a ⊗ ⟨xs, ys⟩
inner-scalarˡ : ∀ n (a : Trit) (xs ys : Vec Trit n) →
  standard-inner-product n (a ·v xs) ys ≡ a ⊗ standard-inner-product n xs ys
inner-scalarˡ n a xs ys =
  begin
    standard-inner-product n (a ·v xs) ys
  ≡⟨ cong (λ v → standard-inner-product n v ys)
          (sym (+v-identityʳ n (a ·v xs))) ⟩
    standard-inner-product n (a ·v xs +v 0⃗ n) ys
  ≡⟨ inner-linearˡ n a xs (0⃗ n) ys ⟩
    (a ⊗ standard-inner-product n xs ys) ⊕
      standard-inner-product n (0⃗ n) ys
  ≡⟨ cong ((a ⊗ standard-inner-product n xs ys) ⊕_)
          (zero-orthogonal n ys) ⟩
    (a ⊗ standard-inner-product n xs ys) ⊕ T₀
  ≡⟨ ⊕-identityʳ (a ⊗ standard-inner-product n xs ys) ⟩
    a ⊗ standard-inner-product n xs ys
  ∎
  where open ≡-Reasoning

-- 内积右标量: ⟨xs, a ·v ys⟩ ≡ a ⊗ ⟨xs, ys⟩
inner-scalarʳ : ∀ n (a : Trit) (xs ys : Vec Trit n) →
  standard-inner-product n xs (a ·v ys) ≡ a ⊗ standard-inner-product n xs ys
inner-scalarʳ n a xs ys =
  begin
    standard-inner-product n xs (a ·v ys)
  ≡⟨ inner-sym n xs (a ·v ys) ⟩
    standard-inner-product n (a ·v ys) xs
  ≡⟨ inner-scalarˡ n a ys xs ⟩
    a ⊗ standard-inner-product n ys xs
  ≡⟨ cong (a ⊗_) (inner-sym n ys xs) ⟩
    a ⊗ standard-inner-product n xs ys
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §5. 正交性定理 — 谱定理的核心
--
-- 定理: 自伴算子的不同特征值的特征向量正交
-- 证明链:
--   λ⊗⟨v,w⟩ = ⟨λv,w⟩ = ⟨Tv,w⟩ = ⟨v,Tw⟩ = ⟨v,μw⟩ = μ⊗⟨v,w⟩
--   故 λ⊗⟨v,w⟩ ≡ μ⊗⟨v,w⟩, 由 λ≠μ 和域的消去律得 ⟨v,w⟩ ≡ T₀
--------------------------------------------------------------------------------

eigenvector-orthogonal : ∀ n (T : Operator n) →
  is-self-adjoint n T →
  ∀ ℓ μ (v w : Vec Trit n) →
  IsEigenpair n T ℓ v →
  IsEigenpair n T μ w →
  ℓ ≢ μ →
  Orthogonal n v w
eigenvector-orthogonal n T sa ℓ μ v w ev ew neq =
  ⊗-eq→zero ℓ μ (standard-inner-product n v w) chain neq
  where
    chain : ℓ ⊗ standard-inner-product n v w ≡
            μ ⊗ standard-inner-product n v w
    chain =
      begin
        ℓ ⊗ standard-inner-product n v w
      ≡⟨ sym (inner-scalarˡ n ℓ v w) ⟩
        standard-inner-product n (ℓ ·v v) w
      ≡⟨ cong (λ u → standard-inner-product n u w) (sym ev) ⟩
        standard-inner-product n (T v) w
      ≡⟨ sa v w ⟩
        standard-inner-product n v (T w)
      ≡⟨ cong (λ u → standard-inner-product n v u) ew ⟩
        standard-inner-product n v (μ ·v w)
      ≡⟨ inner-scalarʳ n μ v w ⟩
        μ ⊗ standard-inner-product n v w
      ∎
      where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §6. n=1 谱定理 — 每个线性算子都是标量乘法
--
-- GF(3)¹ 上, 线性算子 T 完全由 T(e₀) 决定。
-- 设 T(T₁∷[]) = a∷[], 则 T(x∷[]) = a·x 对所有 x。
-- 即 T = a·I, 每个非零向量都是特征向量, 平凡对角化。
--
-- 证明策略:
--   1. T(0) = 0: 由线性性 T(1·0+0) = 1·T(0)+T(0), 穷举 T(0) 的 3 值
--   2. T(1) = a: 由参数传入
--   3. T(2) = 2·a: 由线性性 T(2·1+0) = 2·T(1)+T(0) = 2·a
--------------------------------------------------------------------------------

-- 线性算子保零 (n=1): T(0) = 0
linear-op-zero-1 : ∀ (T : Operator 1) → is-linear-operator 1 T →
  T (T₀ ∷ []) ≡ T₀ ∷ []
linear-op-zero-1 T lin with T (T₀ ∷ []) | lin T₁ (T₀ ∷ []) (T₀ ∷ [])
... | T₀ ∷ [] | _ = refl
... | T₁ ∷ [] | ()
... | T₂ ∷ [] | ()

-- 辅助: 给定 T(1) = a∷[] 的证据, 构造谱分解
spectral-1-go : ∀ (T : Operator 1) (lin : is-linear-operator 1 T)
  (v : Vec Trit 1) → v ≡ T (T₁ ∷ []) →
  Σ Trit (λ a → ∀ (x : Vec Trit 1) → T x ≡ a ·v x)
spectral-1-go T lin (a ∷ []) eq = a , proof
  where
    T-zero : T (T₀ ∷ []) ≡ T₀ ∷ []
    T-zero = linear-op-zero-1 T lin
    T-one : T (T₁ ∷ []) ≡ a ∷ []
    T-one = sym eq
    proof : ∀ x → T x ≡ a ·v x
    -- x = T₀: T(0) = 0 = a·0
    proof (T₀ ∷ []) = trans T-zero (cong (_∷ []) (sym (⊗-zeroʳ a)))
    -- x = T₁: T(1) = a = a·1
    proof (T₁ ∷ []) = trans T-one (cong (_∷ []) (sym (⊗-identityʳ a)))
    -- x = T₂: T(2) = 2·T(1)+T(0) = 2·a = a·2
    proof (T₂ ∷ []) =
      trans (lin T₂ (T₁ ∷ []) (T₀ ∷ []))
            (trans (cong₂ _+v_ (cong (T₂ ·v_) T-one) T-zero)
                   (cong (_∷ []) (trans (⊕-identityʳ (T₂ ⊗ a)) (⊗-comm T₂ a))))

spectral-1 : ∀ (T : Operator 1) → is-linear-operator 1 T →
  Σ Trit (λ a → ∀ (x : Vec Trit 1) → T x ≡ a ·v x)
spectral-1 T lin = spectral-1-go T lin (T (T₁ ∷ [])) refl

--------------------------------------------------------------------------------
-- §7. n=2 内积展开 — 简化计算
--------------------------------------------------------------------------------

-- 二维内积展开: ⟨(x₀,x₁), (y₀,y₁)⟩ ≡ x₀·y₀ + x₁·y₁
inner-2 : ∀ (x₀ x₁ y₀ y₁ : Trit) →
  standard-inner-product 2 (x₀ ∷ x₁ ∷ []) (y₀ ∷ y₁ ∷ []) ≡
  (x₀ ⊗ y₀) ⊕ (x₁ ⊗ y₁)
inner-2 x₀ x₁ y₀ y₁ =
  cong ((x₀ ⊗ y₀) ⊕_) (⊕-identityʳ (x₁ ⊗ y₁))

--------------------------------------------------------------------------------
-- §8. n=2 谱分解实例 — 穷举构造性验证
--------------------------------------------------------------------------------

-- ─── 实例 1: 投影算子 P(x,y) = (x, 0) ───
-- 矩阵 [[1,0],[0,0]], 特征值 1 (e₀) 和 0 (e₁)

proj-op : Operator 2
proj-op (x ∷ y ∷ []) = x ∷ T₀ ∷ []

-- P 是自伴的: ⟨P(f),g⟩ = f₀·g₀ = ⟨f,P(g)⟩
proj-self-adjoint : is-self-adjoint 2 proj-op
proj-self-adjoint (f₀ ∷ f₁ ∷ []) (g₀ ∷ g₁ ∷ []) =
  begin
    standard-inner-product 2 (proj-op (f₀ ∷ f₁ ∷ [])) (g₀ ∷ g₁ ∷ [])
  ≡⟨ inner-2 f₀ T₀ g₀ g₁ ⟩
    (f₀ ⊗ g₀) ⊕ (T₀ ⊗ g₁)
  ≡⟨ cong ((f₀ ⊗ g₀) ⊕_) (⊗-zeroˡ g₁) ⟩
    (f₀ ⊗ g₀) ⊕ T₀
  ≡⟨ sym (cong ((f₀ ⊗ g₀) ⊕_) (⊗-zeroʳ f₁)) ⟩
    (f₀ ⊗ g₀) ⊕ (f₁ ⊗ T₀)
  ≡⟨ sym (inner-2 f₀ f₁ g₀ T₀) ⟩
    standard-inner-product 2 (f₀ ∷ f₁ ∷ []) (proj-op (g₀ ∷ g₁ ∷ []))
  ∎
  where open ≡-Reasoning

-- 特征对: P(e₀) = 1·e₀
proj-eigen-1 : IsEigenpair 2 proj-op T₁ (T₁ ∷ T₀ ∷ [])
proj-eigen-1 = refl

-- 特征对: P(e₁) = 0·e₁
proj-eigen-0 : IsEigenpair 2 proj-op T₀ (T₀ ∷ T₁ ∷ [])
proj-eigen-0 = refl

-- 特征向量正交: ⟨e₀, e₁⟩ = 0 (直接计算)
proj-orth : Orthogonal 2 (T₁ ∷ T₀ ∷ []) (T₀ ∷ T₁ ∷ [])
proj-orth = refl

-- 正交性定理实例化: 由 §5 的一般定理推导
proj-orth-thm : Orthogonal 2 (T₁ ∷ T₀ ∷ []) (T₀ ∷ T₁ ∷ [])
proj-orth-thm = eigenvector-orthogonal 2 proj-op proj-self-adjoint
  T₁ T₀ (T₁ ∷ T₀ ∷ []) (T₀ ∷ T₁ ∷ [])
  proj-eigen-1 proj-eigen-0 (λ ())

-- ─── 实例 2: 全一算子 J(x,y) = (x+y, x+y) ───
-- 矩阵 [[1,1],[1,1]], 特征值 2 ((1,1)) 和 0 ((1,2))

ones-op : Operator 2
ones-op (x ∷ y ∷ []) = (x ⊕ y) ∷ (x ⊕ y) ∷ []

-- J 是自伴的 (证明: 右分配律 + 洗牌引理 + 左分配律)
ones-self-adjoint : is-self-adjoint 2 ones-op
ones-self-adjoint (f₀ ∷ f₁ ∷ []) (g₀ ∷ g₁ ∷ []) =
  begin
    standard-inner-product 2 (ones-op (f₀ ∷ f₁ ∷ [])) (g₀ ∷ g₁ ∷ [])
  ≡⟨ inner-2 (f₀ ⊕ f₁) (f₀ ⊕ f₁) g₀ g₁ ⟩
    ((f₀ ⊕ f₁) ⊗ g₀) ⊕ ((f₀ ⊕ f₁) ⊗ g₁)
  ≡⟨ cong₂ _⊕_ (⊗-distribʳ-⊕ f₀ f₁ g₀) (⊗-distribʳ-⊕ f₀ f₁ g₁) ⟩
    ((f₀ ⊗ g₀) ⊕ (f₁ ⊗ g₀)) ⊕ ((f₀ ⊗ g₁) ⊕ (f₁ ⊗ g₁))
  ≡⟨ ⊕-shuffle (f₀ ⊗ g₀) (f₁ ⊗ g₀) (f₀ ⊗ g₁) (f₁ ⊗ g₁) ⟩
    ((f₀ ⊗ g₀) ⊕ (f₀ ⊗ g₁)) ⊕ ((f₁ ⊗ g₀) ⊕ (f₁ ⊗ g₁))
  ≡⟨ cong₂ _⊕_ (sym (⊗-distribˡ-⊕ f₀ g₀ g₁))
               (sym (⊗-distribˡ-⊕ f₁ g₀ g₁)) ⟩
    (f₀ ⊗ (g₀ ⊕ g₁)) ⊕ (f₁ ⊗ (g₀ ⊕ g₁))
  ≡⟨ sym (inner-2 f₀ f₁ (g₀ ⊕ g₁) (g₀ ⊕ g₁)) ⟩
    standard-inner-product 2 (f₀ ∷ f₁ ∷ []) (ones-op (g₀ ∷ g₁ ∷ []))
  ∎
  where open ≡-Reasoning

-- 特征对: J(1,1) = (2,2) = 2·(1,1)
ones-eigen-2 : IsEigenpair 2 ones-op T₂ (T₁ ∷ T₁ ∷ [])
ones-eigen-2 = refl

-- 特征对: J(1,2) = (0,0) = 0·(1,2) (因为 1+2=0 in GF(3))
ones-eigen-0 : IsEigenpair 2 ones-op T₀ (T₁ ∷ T₂ ∷ [])
ones-eigen-0 = refl

-- 特征向量正交: ⟨(1,1), (1,2)⟩ = 1+2 = 0
ones-orth : Orthogonal 2 (T₁ ∷ T₁ ∷ []) (T₁ ∷ T₂ ∷ [])
ones-orth = refl

-- 正交性定理实例化
ones-orth-thm : Orthogonal 2 (T₁ ∷ T₁ ∷ []) (T₁ ∷ T₂ ∷ [])
ones-orth-thm = eigenvector-orthogonal 2 ones-op ones-self-adjoint
  T₂ T₀ (T₁ ∷ T₁ ∷ []) (T₁ ∷ T₂ ∷ [])
  ones-eigen-2 ones-eigen-0 (λ ())

--------------------------------------------------------------------------------
-- §9. 谱分解记录 — 打包特征值、特征向量、正交性
--------------------------------------------------------------------------------

record SpectralDecomp2 (T : Operator 2) : Set where
  field
    λ₁ λ₂ : Trit
    v₁ v₂ : Vec Trit 2
    eigen₁ : IsEigenpair 2 T λ₁ v₁
    eigen₂ : IsEigenpair 2 T λ₂ v₂
    orth : Orthogonal 2 v₁ v₂
    λ-distinct : λ₁ ≢ λ₂

-- 投影算子的谱分解: P = diag(1, 0)
proj-spectral : SpectralDecomp2 proj-op
proj-spectral = record
  { λ₁ = T₁; λ₂ = T₀
  ; v₁ = T₁ ∷ T₀ ∷ []; v₂ = T₀ ∷ T₁ ∷ []
  ; eigen₁ = refl; eigen₂ = refl
  ; orth = refl; λ-distinct = λ ()
  }

-- 全一算子的谱分解: J = diag(2, 0) 在基 {(1,1), (1,2)} 下
ones-spectral : SpectralDecomp2 ones-op
ones-spectral = record
  { λ₁ = T₂; λ₂ = T₀
  ; v₁ = T₁ ∷ T₁ ∷ []; v₂ = T₁ ∷ T₂ ∷ []
  ; eigen₁ = refl; eigen₂ = refl
  ; orth = refl; λ-distinct = λ ()
  }

--------------------------------------------------------------------------------
-- §10. 恒等/零算子的谱性质 (任意 n)
--------------------------------------------------------------------------------

-- 恒等算子是自伴的
id-self-adjoint : ∀ n → is-self-adjoint n (id-operator n)
id-self-adjoint n f g = refl

-- 零算子是自伴的
zero-self-adjoint : ∀ n → is-self-adjoint n (zero-operator n)
zero-self-adjoint zero [] [] = refl
zero-self-adjoint (suc n) (x ∷ xs) (y ∷ ys) =
  trans (trans (cong (_⊕ standard-inner-product n (0⃗ n) ys) (⊗-zeroˡ y))
               (zero-self-adjoint n xs ys))
        (sym (cong (_⊕ standard-inner-product n xs (0⃗ n)) (⊗-zeroʳ x)))

-- 恒等算子: 每个向量都是特征值 T₁ 的特征向量
id-eigen : ∀ n (v : Vec Trit n) → IsEigenpair n (id-operator n) T₁ v
id-eigen n v = sym (scalar-one n v)

-- 零算子: 每个向量都是特征值 T₀ 的特征向量
zero-eigen : ∀ n (v : Vec Trit n) → IsEigenpair n (zero-operator n) T₀ v
zero-eigen zero [] = refl
zero-eigen (suc n) (x ∷ xs) =
  cong₂ _∷_ (sym (⊗-zeroˡ x)) (zero-eigen n xs)

--------------------------------------------------------------------------------
-- §11. 总结
--------------------------------------------------------------------------------

-- 核心定理列表 (全部 0 postulate, 构造性证明):
--
-- 1. eigenvector-orthogonal: 自伴算子不同特征值的特征向量正交 (任意 n)
-- 2. spectral-1: GF(3)¹ 上每个线性算子都是标量乘法 (完全对角化)
-- 3. proj-spectral: 投影算子 P(x,y)=(x,0) 的谱分解 — 特征值 1, 0
-- 4. ones-spectral: 全一算子 J(x,y)=(x+y,x+y) 的谱分解 — 特征值 2, 0
-- 5. id-self-adjoint / zero-self-adjoint: 恒等/零算子自伴 (任意 n)
-- 6. id-eigen / zero-eigen: 恒等/零算子的特征结构 (任意 n)
--
-- GF(3) 谱定理与 ℂ 谱定理的关键区别:
--   ℂ: 每个自伴算子都可对角化 (特征多项式总有根)
--   GF(3): 自伴算子的特征多项式可能无 GF(3) 根
--     例: [[0,1],[1,1]] 的特征多项式 λ²+2λ+2 在 GF(3) 上不可约
--     判别式 = (0-1)²+4·1·1 = 1+1 = 2, 不是 GF(3) 的平方元
--   因此 GF(3) 上的谱定理是条件性的:
--     若特征多项式分裂 (所有根在 GF(3) 中), 则正交对角化成立
--     本模块形式化了无条件成立的部分 (正交性 + 具体实例)
--------------------------------------------------------------------------------