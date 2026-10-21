{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Analysis.DiscreteFunctional
--
-- 离散泛函分析的最小基石：**对偶空间分离点**（三个坐标泛函联合可区分任意两点）。
--
-- ## 数学背景
--
-- `GF3Func = Trit³` 的对偶空间取为 `GF3Func → Trit`（**不限制线性**——在有限域上
-- 「所有函数」比「线性泛函」更大，分离性对更大的集合成立更强）。
-- 三个**坐标泛函** `proj_j (f) = f 的第 j 个坐标` 已足以分离点：
--
--   `(∀ φ → φ f ≡ φ g) → f ≡ g`
--
-- 连续统里这是 Hahn–Banach 的弱化形态（「对偶空间分离点」）；这里没有分析、没有极限，
-- 只是三个投影的**定义性**事实。
--
-- ## 与 `Foundation.CompletenessTheorem` 的关系
--
-- 该模块把 `FunctionalAnalysis` 的离散载体定为 `GF3Func → Trit`（对偶空间），
-- 并指出缺「概念特有的结构定律」——**本模块补上的正是其中一条**（分离性）。
-- 至此该模块点名的四个缺口中三个已定案（两补一律、一否证），本批补上第四个。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；分离性由三次投影的 `with` 细化直接得出
--------------------------------------------------------------------------------

module Sovereign.Synthesis.Analysis.DiscreteFunctional where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Analytic.ProjectionDifferential using (GF3Func)

-- 对偶空间：所有（不限于线性的）泛函
Dual : Set
Dual = GF3Func → Trit

-- 三个坐标泛函
coord₀ coord₁ coord₂ : Dual
coord₀ (a , _ , _) = a
coord₁ (_ , b , _) = b
coord₂ (_ , _ , c) = c

--------------------------------------------------------------------------------
-- §1. ★ 分离性：任何两个不同的点都有泛函能区分
--------------------------------------------------------------------------------

separating : ∀ (f g : GF3Func) → (∀ φ → φ f ≡ φ g) → f ≡ g
separating (a , b , c) (x , y , z) h with h coord₀ | h coord₁ | h coord₂
... | refl | refl | refl = refl

-- 等价形式：求值映射是单射
evalᶠ : GF3Func → Dual → Trit
evalᶠ f φ = φ f

evalᶠ-injective : ∀ {f g : GF3Func} → (∀ φ → evalᶠ f φ ≡ evalᶠ g φ) → f ≡ g
evalᶠ-injective {f} {g} h = separating f g h

-- 同义反复的等价形态（`f ≡ g` 直接 transport，不需要单独定理）

--------------------------------------------------------------------------------
-- §2. 计算验证
--------------------------------------------------------------------------------

check-coord₀ : coord₀ (T₁ , T₀ , T₂) ≡ T₁
check-coord₀ = refl

-- 两个不同点确实被区分：`(T₀,T₀,T₀)` 与 `(T₁,T₀,T₀)` 在 `proj₀` 上不同
check-separates : coord₀ (T₀ , T₀ , T₀) ≡ coord₀ (T₁ , T₀ , T₀) → ⊥
check-separates ()

--------------------------------------------------------------------------------
-- §3. ★ 定量的分离：**三个泛函就够了**
--
-- `separating` 说「所有泛函能分离点」；这里给出更强的定量形态：
-- 存在**三个**泛函（就是三个坐标投影），只查它们就能判定相等。
-- ⇒ 对偶空间的「分离维数 ≤ 3」，与 `GF3Func = Trit³` 的维数一致。
--------------------------------------------------------------------------------

separating3 : Σ Dual (λ φ₀ → Σ Dual (λ φ₁ → Σ Dual (λ φ₂ →
                 ∀ (f g : GF3Func) → φ₀ f ≡ φ₀ g → φ₁ f ≡ φ₁ g → φ₂ f ≡ φ₂ g → f ≡ g)))
separating3 = coord₀ , coord₁ , coord₂ , λ { (a , b , c) (x , y , z) refl refl refl → refl }
