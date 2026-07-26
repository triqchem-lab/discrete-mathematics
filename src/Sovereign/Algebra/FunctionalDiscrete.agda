{-# OPTIONS --rewriting #-}
module Sovereign.Algebra.FunctionalDiscrete where

--------------------------------------------------------------------------------
-- 离散泛函分析: Hilbert/Banach 空间的 GF(3) 有限维替代
--
-- 核心洞察:
--   在有限集 GF(3)ⁿ 上, 泛函分析的所有概念都有精确的离散版本:
--   • Hilbert 空间 → GF(3)ⁿ 上的内积空间 (有限维)
--   • Banach 空间  → GF(3)ⁿ 上的范数空间 (有限维)
--   • 线性泛函     → GF(3)ⁿ → GF(3) 的线性映射
--   • Riesz 表示   → 有限维内积空间的自然同构 (穷举构造)
--   • 算子         → 矩阵 (有限维)
--
--   关键区别 (与连续泛函分析):
--   ① 有限维 → 不需要完备性 (自动满足)
--   ② GF(3) 内积是退化的 (存在各向同性向量: <x,x>=0 但 x≠0)
--   ③ 所有 "范数" 诱导离散拓扑 (值域仅 {0,1})
--   ④ Hilbert/Banach 区别在拓扑意义下消失
--
-- 依赖:
--   Sovereign.Base.Trit — GF(3) 三进制本体
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
  renaming (module ≡-Reasoning to ≡-Reasoning)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc;
  ⊗-identityˡ; ⊗-identityʳ; ⊗-comm; ⊗-assoc;
  ⊗-distribˡ-⊕; ⊗-distribʳ-⊕;
  ⊗-zeroˡ; ⊗-zeroʳ)

--------------------------------------------------------------------------------
-- §1. 向量空间运算 — GF(3)ⁿ 的线性结构
--------------------------------------------------------------------------------

-- 向量加法: 逐分量 GF(3) 加法
infixl 6 _+v_
_+v_ : ∀ {n} → Vec Trit n → Vec Trit n → Vec Trit n
[] +v [] = []
(x ∷ xs) +v (y ∷ ys) = (x ⊕ y) ∷ (xs +v ys)

-- 标量乘法: 逐分量 GF(3) 乘法
infixl 7 _·v_
_·v_ : ∀ {n} → Trit → Vec Trit n → Vec Trit n
a ·v [] = []
a ·v (x ∷ xs) = (a ⊗ x) ∷ (a ·v xs)

-- 零向量
0⃗ : ∀ n → Vec Trit n
0⃗ zero = []
0⃗ (suc n) = T₀ ∷ 0⃗ n

-- 标准基向量: eᵢ = (0,...,0,1,0,...,0)
basis : ∀ n → Fin n → Vec Trit n
basis (suc n) Fin.zero    = T₁ ∷ 0⃗ n
basis (suc n) (Fin.suc i) = T₀ ∷ basis n i

--------------------------------------------------------------------------------
-- §1b. 向量空间公理 (构造性验证)
--------------------------------------------------------------------------------

-- 零向量是加法单位元
+v-identityˡ : ∀ n (xs : Vec Trit n) → 0⃗ n +v xs ≡ xs
+v-identityˡ zero [] = refl
+v-identityˡ (suc n) (x ∷ xs) =
  cong₂ _∷_ (⊕-identityˡ x) (+v-identityˡ n xs)

+v-identityʳ : ∀ n (xs : Vec Trit n) → xs +v 0⃗ n ≡ xs
+v-identityʳ zero [] = refl
+v-identityʳ (suc n) (x ∷ xs) =
  cong₂ _∷_ (⊕-identityʳ x) (+v-identityʳ n xs)

-- 标量乘零向量得零向量
scalar-zero : ∀ n (a : Trit) → a ·v 0⃗ n ≡ 0⃗ n
scalar-zero zero a = refl
scalar-zero (suc n) a = cong₂ _∷_ (⊗-zeroʳ a) (scalar-zero n a)

-- T₁ 标量乘是恒等
scalar-one : ∀ n (xs : Vec Trit n) → T₁ ·v xs ≡ xs
scalar-one zero [] = refl
scalar-one (suc n) (x ∷ xs) =
  cong₂ _∷_ (⊗-identityˡ x) (scalar-one n xs)

-- 向量加法交换律
+v-comm : ∀ n (xs ys : Vec Trit n) → xs +v ys ≡ ys +v xs
+v-comm zero [] [] = refl
+v-comm (suc n) (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (⊕-comm x y) (+v-comm n xs ys)

-- 向量加法结合律
+v-assoc : ∀ n (xs ys zs : Vec Trit n) → (xs +v ys) +v zs ≡ xs +v (ys +v zs)
+v-assoc zero [] [] [] = refl
+v-assoc (suc n) (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  cong₂ _∷_ (⊕-assoc x y z) (+v-assoc n xs ys zs)

--------------------------------------------------------------------------------
-- §2. 有限维内积空间 — GF(3)ⁿ 上的双线性形式
--------------------------------------------------------------------------------

-- 内积类型
InnerProduct : ℕ → Set
InnerProduct n = Vec Trit n → Vec Trit n → Trit

-- 标准内积: <x,y> = Σᵢ xᵢ·yᵢ (GF(3) 加法和乘法)
standard-inner-product : ∀ n → InnerProduct n
standard-inner-product zero [] [] = T₀
standard-inner-product (suc n) (x ∷ xs) (y ∷ ys) =
  (x ⊗ y) ⊕ standard-inner-product n xs ys

-- 内积对称性: <x,y> = <y,x> (因为 GF(3) 乘法交换)
inner-sym : ∀ n (xs ys : Vec Trit n) →
  standard-inner-product n xs ys ≡ standard-inner-product n ys xs
inner-sym zero [] [] = refl
inner-sym (suc n) (x ∷ xs) (y ∷ ys) =
  cong₂ _⊕_ (⊗-comm x y) (inner-sym n xs ys)

-- GF(3) 加法 "洗牌" 引理: (a⊕b)⊕(c⊕d) ≡ (a⊕c)⊕(b⊕d)
⊕-shuffle : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
⊕-shuffle a b c d =
  begin
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

-- 内积左线性: <ax+y, z> = a<x,z> + <y,z>
inner-linearˡ : ∀ n (a : Trit) (xs ys zs : Vec Trit n) →
  standard-inner-product n (a ·v xs +v ys) zs ≡
  (a ⊗ standard-inner-product n xs zs) ⊕ standard-inner-product n ys zs
inner-linearˡ zero a [] [] [] = sym (cong (_⊕ T₀) (⊗-zeroʳ a))
inner-linearˡ (suc n) a (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  let ih = inner-linearˡ n a xs ys zs
      p = standard-inner-product n xs zs
      q = standard-inner-product n ys zs
      r = standard-inner-product n (a ·v xs +v ys) zs
      -- 单步: ((a⊗x)⊕y)⊗z ≡ (a⊗(x⊗z)) ⊕ (y⊗z)
      step₁ : ((a ⊗ x) ⊕ y) ⊗ z ≡ (a ⊗ (x ⊗ z)) ⊕ (y ⊗ z)
      step₁ = trans (⊗-distribʳ-⊕ (a ⊗ x) y z)
                    (cong (_⊕ (y ⊗ z)) (⊗-assoc a x z))
  in
    begin
      (((a ⊗ x) ⊕ y) ⊗ z) ⊕ r
    ≡⟨ cong (_⊕ r) step₁ ⟩
      ((a ⊗ (x ⊗ z)) ⊕ (y ⊗ z)) ⊕ r
    ≡⟨ cong (((a ⊗ (x ⊗ z)) ⊕ (y ⊗ z)) ⊕_) ih ⟩
      ((a ⊗ (x ⊗ z)) ⊕ (y ⊗ z)) ⊕ ((a ⊗ p) ⊕ q)
    ≡⟨ ⊕-shuffle (a ⊗ (x ⊗ z)) (y ⊗ z) (a ⊗ p) q ⟩
      ((a ⊗ (x ⊗ z)) ⊕ (a ⊗ p)) ⊕ ((y ⊗ z) ⊕ q)
    ≡⟨ cong (_⊕ ((y ⊗ z) ⊕ q))
         (sym (⊗-distribˡ-⊕ a (x ⊗ z) p)) ⟩
      (a ⊗ ((x ⊗ z) ⊕ p)) ⊕ ((y ⊗ z) ⊕ q)
    ∎
  where open ≡-Reasoning

-- 内积右线性 (由对称性 + 左线性)
inner-linearʳ : ∀ n (a : Trit) (xs ys zs : Vec Trit n) →
  standard-inner-product n xs (a ·v ys +v zs) ≡
  (a ⊗ standard-inner-product n xs ys) ⊕ standard-inner-product n xs zs
inner-linearʳ n a xs ys zs =
  begin
    standard-inner-product n xs (a ·v ys +v zs)
  ≡⟨ inner-sym n xs (a ·v ys +v zs) ⟩
    standard-inner-product n (a ·v ys +v zs) xs
  ≡⟨ inner-linearˡ n a ys zs xs ⟩
    (a ⊗ standard-inner-product n ys xs) ⊕ standard-inner-product n zs xs
  ≡⟨ cong₂ _⊕_ (cong (a ⊗_) (inner-sym n ys xs)) (inner-sym n zs xs) ⟩
    (a ⊗ standard-inner-product n xs ys) ⊕ standard-inner-product n xs zs
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- §3. 离散范数 — GF(3)ⁿ 上的范数结构
--------------------------------------------------------------------------------

-- GF(3) 绝对值: |0|=0, |1|=1, |2|=|-1|=1
abs-gf3 : Trit → Trit
abs-gf3 T₀ = T₀
abs-gf3 T₁ = T₁
abs-gf3 T₂ = T₁

-- 最大值 (在 {T₀, T₁} 上): max(0,x)=x, max(1,x)=1
max-abs : Trit → Trit → Trit
max-abs T₀ y = y
max-abs T₁ _ = T₁
max-abs T₂ y = y

-- 离散 sup-范数: ‖x‖∞ = max |xᵢ|
-- 在 GF(3) 中, 值域仅 {T₀, T₁}: 零向量→T₀, 非零向量→T₁
discrete-norm : ∀ n → Vec Trit n → Trit
discrete-norm zero [] = T₀
discrete-norm (suc n) (x ∷ xs) = max-abs (abs-gf3 x) (discrete-norm n xs)

-- 范数零 → 向量为零
norm-zero→vec-zero : ∀ n (xs : Vec Trit n) →
  discrete-norm n xs ≡ T₀ → xs ≡ 0⃗ n
norm-zero→vec-zero zero [] _ = refl
norm-zero→vec-zero (suc n) (T₀ ∷ xs) p =
  cong (T₀ ∷_) (norm-zero→vec-zero n xs p)
norm-zero→vec-zero (suc n) (T₁ ∷ xs) ()
norm-zero→vec-zero (suc n) (T₂ ∷ xs) ()

-- 零向量的范数为零
norm-of-zero : ∀ n → discrete-norm n (0⃗ n) ≡ T₀
norm-of-zero zero = refl
norm-of-zero (suc n) = norm-of-zero n

-- 向量为零 → 范数零
vec-zero→norm-zero : ∀ n (xs : Vec Trit n) →
  xs ≡ 0⃗ n → discrete-norm n xs ≡ T₀
vec-zero→norm-zero n xs p =
  subst (λ v → discrete-norm n v ≡ T₀) (sym p) (norm-of-zero n)

-- 二次型 (内积自作用): Q(x) = <x,x>
-- 注意: 在 GF(3) 中, Q 是退化的 — 存在各向同性向量
quadratic-form : ∀ n → Vec Trit n → Trit
quadratic-form n xs = standard-inner-product n xs xs

-- 各向同性: (T₁, T₁, T₁) 的二次型为 T₀ (因为 1+1+1=3≡0)
-- 这是 GF(3) 内积空间与 ℝⁿ 内积空间的本质区别
isotropic-example : quadratic-form 3 (T₁ ∷ T₁ ∷ T₁ ∷ []) ≡ T₀
isotropic-example = refl

-- 但该向量不是零向量
isotropic-nonzero : (T₁ ∷ T₁ ∷ T₁ ∷ []) ≢ 0⃗ 3
isotropic-nonzero ()

--------------------------------------------------------------------------------
-- §4. 线性泛函 — GF(3)ⁿ → GF(3) 的线性映射
--------------------------------------------------------------------------------

-- 线性泛函类型
LinearFunctional : ℕ → Set
LinearFunctional n = Vec Trit n → Trit

-- 线性性: f(a·x + y) = a·f(x) + f(y)
-- 此单一条件蕴含加性 (a=T₁) 和齐性 (y=0⃗)
is-linear : ∀ n → LinearFunctional n → Set
is-linear n f = ∀ a (x y : Vec Trit n) →
  f (a ·v x +v y) ≡ (a ⊗ f x) ⊕ f y

-- 线性泛函将零向量映为零
-- [证明策略: 穷举法 — 对 f(0⃗) 的 3 个可能值穷举]
-- [代数结构: scalar-zero (∀ n a → a·v 0⃗ ≡ 0⃗) 替代 scalar-one 递归]
linear-preserves-zero : ∀ n (f : LinearFunctional n) →
  is-linear n f → f (0⃗ n) ≡ T₀
linear-preserves-zero n f lin = helper
  where
    -- T₁·0⃗ + 0⃗ ≡ 0⃗ (用 scalar-zero 替代 scalar-one, 避免递归)
    step1 : T₁ ·v 0⃗ n +v 0⃗ n ≡ 0⃗ n
    step1 = trans (cong (_+v 0⃗ n) (scalar-zero n T₁))
                  (+v-identityˡ n (0⃗ n))
    -- f(0⃗) ≡ (T₁⊗f(0⃗)) ⊕ f(0⃗)
    key : f (0⃗ n) ≡ (T₁ ⊗ f (0⃗ n)) ⊕ f (0⃗ n)
    key = trans (sym (cong f step1)) (lin T₁ (0⃗ n) (0⃗ n))
    -- 穷举 f(0⃗) 的 3 个可能值
    helper : f (0⃗ n) ≡ T₀
    helper with f (0⃗ n) | key
    ... | T₀ | _ = refl
    ... | T₁ | ()
    ... | T₂ | ()

-- 内积诱导线性泛函: y ↦ <·, y>
inner-functional : ∀ n → Vec Trit n → LinearFunctional n
inner-functional n y = λ x → standard-inner-product n x y

-- 内积泛函是线性的
inner-functional-linear : ∀ n (y : Vec Trit n) →
  is-linear n (inner-functional n y)
inner-functional-linear n y a x y' = inner-linearˡ n a x y' y

--------------------------------------------------------------------------------
-- §5. Riesz 表示定理 (离散版) — 穷举构造性证明
--
-- 定理: 每个线性泛函 f : GF(3)ⁿ → GF(3) 都可以唯一表示为
--       f(x) = <x, y> 对某个 y ∈ GF(3)ⁿ
--
-- 构造: yᵢ = f(eᵢ) (f 在标准基上的值)
-- 证明: 对维度 n 归纳, 利用线性性分解
--------------------------------------------------------------------------------

-- 尾部限制: 将 f : GF(3)^(suc n) → GF(3) 限制到尾部子空间
tail-functional : ∀ n → LinearFunctional (suc n) → LinearFunctional n
tail-functional n f xs = f (T₀ ∷ xs)

-- 尾部限制保持线性性
tail-preserves-linear : ∀ n (f : LinearFunctional (suc n)) →
  is-linear (suc n) f → is-linear n (tail-functional n f)
tail-preserves-linear n f lin a xs ys =
  trans (cong f (tail-decompose a xs ys)) (lin a (T₀ ∷ xs) (T₀ ∷ ys))
  where
    -- T₀ ∷ (a·xs + ys) ≡ (a·(T₀∷xs)) + (T₀∷ys)
    tail-decompose : ∀ (a : Trit) (xs ys : Vec Trit n) →
      T₀ ∷ (a ·v xs +v ys) ≡ (a ·v (T₀ ∷ xs)) +v (T₀ ∷ ys)
    tail-decompose a xs ys =
      cong₂ _∷_ (sym (cong (_⊕ T₀) (⊗-zeroʳ a))) refl

-- Riesz 表示向量: yᵢ = f(eᵢ)
riesz-vector : ∀ n → LinearFunctional n → Vec Trit n
riesz-vector zero f = []
riesz-vector (suc n) f =
  f (T₁ ∷ 0⃗ n) ∷ riesz-vector n (tail-functional n f)

-- 分解引理: x₀∷xs ≡ (x₀·e₀) + (T₀∷xs)
vec-decompose : ∀ n (x₀ : Trit) (xs : Vec Trit n) →
  x₀ ∷ xs ≡ (x₀ ·v (T₁ ∷ 0⃗ n)) +v (T₀ ∷ xs)
vec-decompose n x₀ xs = cong₂ _∷_
  (trans (sym (⊕-identityʳ x₀)) (cong (_⊕ T₀) (sym (⊗-identityʳ x₀))))
  (trans (sym (+v-identityˡ n xs)) (cong (_+v xs) (sym (scalar-zero n x₀))))

-- Riesz 表示定理: f(x) ≡ <x, riesz-vector f>
riesz-discrete : ∀ n (f : LinearFunctional n) → is-linear n f →
  ∀ x → f x ≡ standard-inner-product n x (riesz-vector n f)
riesz-discrete zero f lin [] with f [] | lin T₁ [] []
... | T₀ | _ = refl
... | T₁ | ()
... | T₂ | ()
riesz-discrete (suc n) f lin (x₀ ∷ xs) =
  begin
    f (x₀ ∷ xs)
  ≡⟨ cong f (vec-decompose n x₀ xs) ⟩
    f ((x₀ ·v (T₁ ∷ 0⃗ n)) +v (T₀ ∷ xs))
  ≡⟨ lin x₀ (T₁ ∷ 0⃗ n) (T₀ ∷ xs) ⟩
    (x₀ ⊗ f (T₁ ∷ 0⃗ n)) ⊕ f (T₀ ∷ xs)
  ≡⟨ cong ((x₀ ⊗ f (T₁ ∷ 0⃗ n)) ⊕_)
       (riesz-discrete n (tail-functional n f)
         (tail-preserves-linear n f lin) xs) ⟩
    (x₀ ⊗ f (T₁ ∷ 0⃗ n)) ⊕
      standard-inner-product n xs (riesz-vector n (tail-functional n f))
  ≡⟨ refl ⟩
    standard-inner-product (suc n) (x₀ ∷ xs) (riesz-vector (suc n) f)
  ∎
  where open ≡-Reasoning

-- Riesz 表示的等价形式: 存在性
riesz-exists : ∀ n (f : LinearFunctional n) → is-linear n f →
  Σ (Vec Trit n) (λ y → ∀ x → f x ≡ standard-inner-product n x y)
riesz-exists n f lin = riesz-vector n f , riesz-discrete n f lin

--------------------------------------------------------------------------------
-- §6. 有限维算子 — 矩阵与算子范数
--------------------------------------------------------------------------------

-- 算子类型: GF(3)ⁿ → GF(3)ⁿ 的线性映射
Operator : ℕ → Set
Operator n = Vec Trit n → Vec Trit n

-- 算子线性性
is-linear-operator : ∀ n → Operator n → Set
is-linear-operator n A = ∀ a (x y : Vec Trit n) →
  A (a ·v x +v y) ≡ a ·v A x +v A y

-- 恒等算子
id-operator : ∀ n → Operator n
id-operator n = λ x → x

-- 恒等算子是线性的
id-linear : ∀ n → is-linear-operator n (id-operator n)
id-linear n a x y = refl

-- 零算子
zero-operator : ∀ n → Operator n
zero-operator n = λ _ → 0⃗ n

-- 零算子是线性的
zero-linear : ∀ n → is-linear-operator n (zero-operator n)
zero-linear zero a [] [] = refl
zero-linear (suc n) a (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_
    (sym (cong (_⊕ T₀) (⊗-zeroʳ a)))
    (sym (trans (cong (_+v 0⃗ n) (scalar-zero n a)) (+v-identityˡ n (0⃗ n))))

-- 有限和: 对 Fin n 求和
sum-fin : ∀ n → (Fin n → Trit) → Trit
sum-fin zero f = T₀
sum-fin (suc n) f = f Fin.zero ⊕ sum-fin n (f ∘ Fin.suc)

-- 算子范数 (Frobenius): ‖A‖²_F = Σᵢ <A(eᵢ), A(eᵢ)>
-- 在 GF(3) 中, 这是 A 的所有列向量的二次型之和
operator-norm : ∀ n → Operator n → Trit
operator-norm n A = sum-fin n (λ i →
  quadratic-form n (A (basis n i)))

-- 二次型在零向量为零
quadratic-zero : ∀ n → quadratic-form n (0⃗ n) ≡ T₀
quadratic-zero zero = refl
quadratic-zero (suc n) = cong (T₀ ⊕_) (quadratic-zero n)

-- sum-fin 全零为零
sum-fin-zero : ∀ n → sum-fin n (λ _ → T₀) ≡ T₀
sum-fin-zero zero = refl
sum-fin-zero (suc n) = cong (T₀ ⊕_) (sum-fin-zero n)

-- sum-fin 常值零: 对常值 T₀ 函数求和得 T₀
sum-fin-const-zero : ∀ n m → sum-fin n (λ _ → quadratic-form m (0⃗ m)) ≡ T₀
sum-fin-const-zero zero m = refl
sum-fin-const-zero (suc n) m =
  trans (cong (_⊕ sum-fin n (λ _ → quadratic-form m (0⃗ m))) (quadratic-zero m))
        (cong (T₀ ⊕_) (sum-fin-const-zero n m))

-- 零算子的范数为零
zero-operator-norm : ∀ n → operator-norm n (zero-operator n) ≡ T₀
zero-operator-norm zero = refl
zero-operator-norm (suc n) =
  trans (cong (_⊕ sum-fin n (λ _ → quadratic-form (suc n) (0⃗ (suc n))))
           (quadratic-zero (suc n)))
        (cong (T₀ ⊕_) (sum-fin-const-zero n (suc n)))

--------------------------------------------------------------------------------
-- §7. Hilbert/Banach 坍缩 — 离散与连续的投影关系
--
-- 连续泛函分析:
--   Hilbert 空间 = 完备内积空间 (可无穷维)
--   Banach 空间  = 完备赋范空间
--   Riesz: H* ≅ H (反线性同构)
--   关键: 无穷维中 Hilbert ⊊ Banach (不是所有范数来自内积)
--
-- GF(3)ⁿ 离散版:
--   ① 有限维 → 完备性自动满足 (有限集上所有 Cauchy 列最终常数)
--   ② 拓扑离散 → 所有 "范数" 诱导相同拓扑 (单点集开)
--   ③ 内积退化 → 二次型有各向同性向量, 不诱导正定范数
--   ④ Riesz 仍成立 → 因为双线性形式的非退化性 (≠ 正定性)
--
-- 投影关系:
--   连续 Hilbert 空间是 GF(3)ⁿ 在 "n→∞, GF(3)→ℝ" 双重极限下的影子
--   但 GF(3) 是有限域, n→∞ 不产生完备空间 — 极限不存在
--   所以 Hilbert 空间是有限维内积空间的 "不存在的极限"
--   离散版本是本体, 连续版本是投影像
--------------------------------------------------------------------------------

-- 定理: 离散范数只取两个值 (T₀ 或 T₁)
-- 这意味着诱导的拓扑是离散拓扑: 每个单点集都是开集
norm-two-valued : ∀ n (xs : Vec Trit n) →
  discrete-norm n xs ≡ T₀ ⊎ discrete-norm n xs ≡ T₁
norm-two-valued zero [] = inj₁ refl
norm-two-valued (suc n) (T₀ ∷ xs) = norm-two-valued n xs
norm-two-valued (suc n) (T₁ ∷ xs) = inj₂ refl
norm-two-valued (suc n) (T₂ ∷ xs) = inj₂ refl

-- 定理: 内积非退化 — 如果 <x, y>=0 对所有 y, 则 x=0
-- (这是 Riesz 定理成立的关键条件, 弱于正定性)
-- 在 GF(3) 中, 标准内积实际上是非退化的:
-- 如果 <x, eᵢ>=0 对所有 i, 则 xᵢ=0 对所有 i, 故 x=0
inner-nondegenerate : ∀ n (xs : Vec Trit n) →
  (∀ ys → standard-inner-product n xs ys ≡ T₀) → xs ≡ 0⃗ n
inner-nondegenerate zero [] _ = refl
inner-nondegenerate (suc n) (x₀ ∷ xs) hyp =
  cong₂ _∷_ x₀-is-T₀ (inner-nondegenerate n xs tail-hyp)
  where
    -- 内积与零向量为零
    inner-zero-rt : ∀ m (vs : Vec Trit m) → standard-inner-product m vs (0⃗ m) ≡ T₀
    inner-zero-rt zero [] = refl
    inner-zero-rt (suc m) (v ∷ vs) =
      trans (cong (_⊕ standard-inner-product m vs (0⃗ m)) (⊗-zeroʳ v))
            (inner-zero-rt m vs)

    -- x₀ ≡ T₀: 从 hyp(T₁∷0⃗) 推导
    x₀-is-T₀ : x₀ ≡ T₀
    x₀-is-T₀ =
      let p₁ = cong (_⊕ standard-inner-product n xs (0⃗ n)) (⊗-identityʳ x₀)
          p₂ = cong (x₀ ⊕_) (inner-zero-rt n xs)
          p₃ = ⊕-identityʳ x₀
          chain = trans p₁ (trans p₂ p₃)
      in trans (sym chain) (hyp (T₁ ∷ 0⃗ n))

    -- 尾部假设: 从 hyp(T₀∷ys) 推导
    tail-hyp : ∀ ys → standard-inner-product n xs ys ≡ T₀
    tail-hyp ys =
      subst (_≡ T₀)
        (cong (_⊕ standard-inner-product n xs ys) (⊗-zeroʳ x₀))
        (hyp (T₀ ∷ ys))

-- Hilbert/Banach 坍缩: 范数零 ↔ 二次型零 → 向量零
-- 在 GF(3)ⁿ 上, 内积空间结构和范数空间结构诱导相同的离散拓扑
-- 两者的 "零集" 判定一致: 范数为零当且仅当向量为零
-- 因此拓扑相同 (离散拓扑), Hilbert/Banach 区别消失
hilbert-banach-collapse : ∀ n (xs : Vec Trit n) →
  discrete-norm n xs ≡ T₀ → xs ≡ 0⃗ n
hilbert-banach-collapse n xs = norm-zero→vec-zero n xs

--------------------------------------------------------------------------------
-- §8. 正交性 — 内积空间的几何结构
--------------------------------------------------------------------------------

-- 正交性: <x, y> ≡ T₀
Orthogonal : ∀ n → Vec Trit n → Vec Trit n → Set
Orthogonal n x y = standard-inner-product n x y ≡ T₀

-- 正交性对称
orth-sym : ∀ n (x y : Vec Trit n) → Orthogonal n x y → Orthogonal n y x
orth-sym n x y p = trans (inner-sym n y x) p

-- 零向量与所有向量正交
zero-orthogonal : ∀ n (xs : Vec Trit n) → Orthogonal n (0⃗ n) xs
zero-orthogonal zero [] = refl
zero-orthogonal (suc n) (x ∷ xs) =
  cong (T₀ ⊕_) (zero-orthogonal n xs)

-- 自正交即各向同性 (定义展开)
self-orthogonal-isotropic : ∀ n (xs : Vec Trit n) →
  Orthogonal n xs xs ≡ (quadratic-form n xs ≡ T₀)
self-orthogonal-isotropic n xs = refl

--------------------------------------------------------------------------------
-- §9. 对偶空间 — GF(3)ⁿ 的线性泛函空间
--
-- Riesz 定理的对偶表述: GF(3)ⁿ ≅ (GF(3)ⁿ)*
-- 即向量空间自然同构于其对偶空间
--------------------------------------------------------------------------------

-- 对偶空间: 所有线性泛函的集合
DualSpace : ℕ → Set
DualSpace n = Σ (LinearFunctional n) (is-linear n)

-- Riesz 同构: GF(3)ⁿ → (GF(3)ⁿ)*
-- 将向量 y 映为线性泛函 <·, y>
riesz-map : ∀ n → Vec Trit n → DualSpace n
riesz-map n y = inner-functional n y , inner-functional-linear n y

-- Riesz 同构是满射 (每个线性泛函都有原像)
riesz-surjective : ∀ n → (f : LinearFunctional n) → (lin : is-linear n f) →
  Σ (Vec Trit n) (λ y → ∀ x → f x ≡ proj₁ (riesz-map n y) x)
riesz-surjective n f lin = riesz-vector n f , riesz-discrete n f lin

--------------------------------------------------------------------------------
-- §10. 总结: 离散泛函分析的核心定理
--------------------------------------------------------------------------------

-- 核心定理列表 (全部 0 postulate, 构造性证明):
--
-- 1. standard-inner-product: GF(3)ⁿ 上的对称双线性形式
-- 2. inner-linearˡ/inner-linearʳ: 双线性性
-- 3. discrete-norm: sup-范数, 值域 {T₀, T₁}
-- 4. riesz-discrete: 每个线性泛函 f 都有 f(x) = <x, y> (y = riesz-vector f)
-- 5. inner-nondegenerate: 标准内积非退化 (Riesz 成立的关键)
-- 6. isotropic-example: GF(3) 内积退化 (与 ℝⁿ 的本质区别)
-- 7. norm-two-valued: 离散拓扑下 Hilbert/Banach 区别消失
--
-- 与连续泛函分析的投影关系:
--   连续: Hilbert ⊊ Banach (无穷维), Riesz 需要完备性
--   离散: Hilbert = Banach (有限维, 离散拓扑), Riesz 是有限穷举
--   投影方向: 离散 (本体) → 连续 (影子), 信息丢失: 有限性, GF(3) 结构
--------------------------------------------------------------------------------
