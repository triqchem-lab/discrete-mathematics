{-# OPTIONS --rewriting #-}
module Sovereign.Analysis.TestRiesz where

--------------------------------------------------------------------------------
-- Riesz 表示定理测试用例 — n=2 的 GF(3)² 向量空间 (9 个元素)
--
-- 测试内容:
--   1. 坐标泛函 coord0(f) = f(0), 验证 riesz-vector coord0 ≡ e₀
--   2. 求和泛函 sum(f) = f(0)+f(1), 验证 riesz-vector sum ≡ (1,1)
--   3. 唯一性: ∀ v1 v2 → (∀ f → f(v1)≡f(v2)) → v1≡v2
--
-- 依赖:
--   Sovereign.Algebra.FunctionalDiscrete — GF(3)ⁿ 离散泛函分析
--
-- 约束:
--   • 不用递归/归纳 — 所有证明为 n=2 的穷举/计算
--   • 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc;
  ⊗-identityˡ; ⊗-identityʳ; ⊗-comm;
  ⊗-distribˡ-⊕; ⊗-zeroˡ; ⊗-zeroʳ)

open import Sovereign.Algebra.FunctionalDiscrete using (
  -- 向量空间运算
  _+v_; _·v_; 0⃗; basis;
  -- 内积
  standard-inner-product; inner-sym; inner-linearˡ; inner-linearʳ;
  ⊕-shuffle;
  -- 线性泛函
  LinearFunctional; is-linear;
  -- Riesz 表示
  riesz-vector; riesz-discrete; riesz-exists;
  -- 非退化性
  inner-nondegenerate;
  -- 向量空间公理
  +v-identityˡ; +v-identityʳ; scalar-zero; scalar-one)

--------------------------------------------------------------------------------
-- §1. 测试用线性泛函定义 (n=2)
--------------------------------------------------------------------------------

-- 坐标泛函: coord0(v) = v 的第 0 个分量
coord0 : LinearFunctional 2
coord0 (x ∷ y ∷ []) = x

-- 坐标泛函: coord1(v) = v 的第 1 个分量
coord1 : LinearFunctional 2
coord1 (x ∷ y ∷ []) = y

-- 求和泛函: sum-func(v) = v₀ + v₁ (GF(3) 加法)
sum-func : LinearFunctional 2
sum-func (x ∷ y ∷ []) = x ⊕ y

--------------------------------------------------------------------------------
-- §2. 线性性验证 (穷举, 无递归)
--------------------------------------------------------------------------------

-- coord0 是线性的: coord0(a·x + y) ≡ a⊗coord0(x) ⊕ coord0(y)
-- 展开: (a⊗x₀ ⊕ y₀) ≡ (a⊗x₀) ⊕ y₀ — 定义等价
coord0-linear : is-linear 2 coord0
coord0-linear a (x₀ ∷ x₁ ∷ []) (y₀ ∷ y₁ ∷ []) = refl

-- coord1 是线性的: 同理
coord1-linear : is-linear 2 coord1
coord1-linear a (x₀ ∷ x₁ ∷ []) (y₀ ∷ y₁ ∷ []) = refl

-- sum-func 是线性的:
-- LHS: (a⊗x₀ ⊕ y₀) ⊕ (a⊗x₁ ⊕ y₁)
-- RHS: (a ⊗ (x₀ ⊕ x₁)) ⊕ (y₀ ⊕ y₁)
-- 证明: ⊕-shuffle 重排 + ⊗-distribˡ-⊕ 分配律
sum-func-linear : is-linear 2 sum-func
sum-func-linear a (x₀ ∷ x₁ ∷ []) (y₀ ∷ y₁ ∷ []) =
  trans (⊕-shuffle (a ⊗ x₀) y₀ (a ⊗ x₁) y₁)
        (cong (_⊕ (y₀ ⊕ y₁)) (sym (⊗-distribˡ-⊕ a x₀ x₁)))

--------------------------------------------------------------------------------
-- §3. Riesz 表示向量验证 — 计算归约 (refl)
--------------------------------------------------------------------------------

-- 测试 1: coord0 的 Riesz 向量是 e₀ = (T₁, T₀)
-- 计算: riesz-vector 2 coord0
--   = coord0(T₁∷T₀∷[]) ∷ riesz-vector 1 (tail coord0)
--   = T₁ ∷ coord0(T₀∷T₁∷[]) ∷ []
--   = T₁ ∷ T₀ ∷ []
test-riesz-coord0 : riesz-vector 2 coord0 ≡ T₁ ∷ T₀ ∷ []
test-riesz-coord0 = refl

-- 测试 2: sum-func 的 Riesz 向量是 (T₁, T₁)
-- 计算: riesz-vector 2 sum-func
--   = sum-func(T₁∷T₀∷[]) ∷ riesz-vector 1 (tail sum-func)
--   = (T₁⊕T₀) ∷ sum-func(T₀∷T₁∷[]) ∷ []
--   = T₁ ∷ (T₀⊕T₁) ∷ []
--   = T₁ ∷ T₁ ∷ []
test-riesz-sum : riesz-vector 2 sum-func ≡ T₁ ∷ T₁ ∷ []
test-riesz-sum = refl

-- 测试: coord1 的 Riesz 向量是 e₁ = (T₀, T₁)
test-riesz-coord1 : riesz-vector 2 coord1 ≡ T₀ ∷ T₁ ∷ []
test-riesz-coord1 = refl

--------------------------------------------------------------------------------
-- §4. Riesz 表示定理实例化 — 泛函 ≡ 内积
--------------------------------------------------------------------------------

-- coord0(x) ≡ ⟨x, (T₁,T₀)⟩ 对所有 x
test-coord0-repr : ∀ x → coord0 x ≡ standard-inner-product 2 x (T₁ ∷ T₀ ∷ [])
test-coord0-repr = riesz-discrete 2 coord0 coord0-linear

-- sum-func(x) ≡ ⟨x, (T₁,T₁)⟩ 对所有 x
test-sum-repr : ∀ x → sum-func x ≡ standard-inner-product 2 x (T₁ ∷ T₁ ∷ [])
test-sum-repr = riesz-discrete 2 sum-func sum-func-linear

-- coord1(x) ≡ ⟨x, (T₀,T₁)⟩ 对所有 x
test-coord1-repr : ∀ x → coord1 x ≡ standard-inner-product 2 x (T₀ ∷ T₁ ∷ [])
test-coord1-repr = riesz-discrete 2 coord1 coord1-linear

--------------------------------------------------------------------------------
-- §5. 具体向量的内积计算验证 (refl)
--------------------------------------------------------------------------------

-- ⟨e₀, e₀⟩ = T₁ (标准基自内积)
test-inner-e0-e0 : standard-inner-product 2 (T₁ ∷ T₀ ∷ []) (T₁ ∷ T₀ ∷ []) ≡ T₁
test-inner-e0-e0 = refl

-- ⟨e₁, e₁⟩ = T₁
test-inner-e1-e1 : standard-inner-product 2 (T₀ ∷ T₁ ∷ []) (T₀ ∷ T₁ ∷ []) ≡ T₁
test-inner-e1-e1 = refl

-- ⟨e₀, e₁⟩ = T₀ (标准基正交)
test-inner-e0-e1 : standard-inner-product 2 (T₁ ∷ T₀ ∷ []) (T₀ ∷ T₁ ∷ []) ≡ T₀
test-inner-e0-e1 = refl

-- ⟨(1,1), (1,1)⟩ = T₁⊕T₁ = T₂ (GF(3) 中 1+1=2)
test-inner-sum-sum : standard-inner-product 2 (T₁ ∷ T₁ ∷ []) (T₁ ∷ T₁ ∷ []) ≡ T₂
test-inner-sum-sum = refl

-- ⟨(1,1), (1,2)⟩ = T₁⊕T₂ = T₀ (GF(3) 中 1+2=0)
test-inner-orth : standard-inner-product 2 (T₁ ∷ T₁ ∷ []) (T₁ ∷ T₂ ∷ []) ≡ T₀
test-inner-orth = refl

--------------------------------------------------------------------------------
-- §6. 唯一性测试 — 对偶空间分离点
--
-- 定理: 如果两个向量在所有线性泛函下给出相同值, 则它们相等。
-- 证明策略: 用坐标泛函 coord0, coord1 分离分量 (无递归/归纳)
--------------------------------------------------------------------------------

riesz-unique-2 : ∀ (v1 v2 : Vec Trit 2) →
  (∀ (f : LinearFunctional 2) → is-linear 2 f → f v1 ≡ f v2) →
  v1 ≡ v2
riesz-unique-2 (a ∷ b ∷ []) (c ∷ d ∷ []) hyp =
  cong₂ _∷_ (hyp coord0 coord0-linear)
            (cong₂ _∷_ (hyp coord1 coord1-linear) refl)

--------------------------------------------------------------------------------
-- §7. 存在性证据打包
--------------------------------------------------------------------------------

-- Riesz 存在性: coord0 有表示向量
coord0-exists : Σ (Vec Trit 2) (λ y → ∀ x → coord0 x ≡ standard-inner-product 2 x y)
coord0-exists = riesz-exists 2 coord0 coord0-linear

-- Riesz 存在性: sum-func 有表示向量
sum-exists : Σ (Vec Trit 2) (λ y → ∀ x → sum-func x ≡ standard-inner-product 2 x y)
sum-exists = riesz-exists 2 sum-func sum-func-linear

-- 存在性向量的具体值验证
coord0-witness-is-e0 : proj₁ coord0-exists ≡ T₁ ∷ T₀ ∷ []
coord0-witness-is-e0 = refl

sum-witness-is-ones : proj₁ sum-exists ≡ T₁ ∷ T₁ ∷ []
sum-witness-is-ones = refl
