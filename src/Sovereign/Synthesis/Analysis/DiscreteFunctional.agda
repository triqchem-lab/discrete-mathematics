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
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; ⊕-assoc; ⊕-comm;
  ⊕-identityʳ; ⊗-identityʳ; ⊗-zeroʳ)
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

--------------------------------------------------------------------------------
-- §4. ★ 线性泛函
--
-- `Linear φ` = 对 `⊕ₚ` 可加 + 对逐点标量乘齐次。三个坐标泛函都线性（定义性）。
--------------------------------------------------------------------------------

_⊕ₚ_ : GF3Func → GF3Func → GF3Func
(a , b , c) ⊕ₚ (x , y , z) = (a ⊕ x) , (b ⊕ y) , (c ⊕ z)

_•_ : Trit → GF3Func → GF3Func
k • (a , b , c) = (k ⊗ a) , (k ⊗ b) , (k ⊗ c)

Linear : Dual → Set
Linear φ = (∀ f g → φ (f ⊕ₚ g) ≡ φ f ⊕ φ g)
         × (∀ (k : Trit) (f : GF3Func) → φ (k • f) ≡ k ⊗ φ f)

-- 三个坐标泛函都线性（两分量均定义性）
coord₀-linear : Linear coord₀
coord₀-linear = (λ _ _ → refl) , (λ _ _ → refl)

coord₁-linear : Linear coord₁
coord₁-linear = (λ _ _ → refl) , (λ _ _ → refl)

coord₂-linear : Linear coord₂
coord₂-linear = (λ _ _ → refl) , (λ _ _ → refl)

--------------------------------------------------------------------------------
-- §5. ★★ 对偶维数定理：线性泛函**由三个基值决定**
--
-- `φ (a,b,c) = a⊗φe₀ ⊕ (b⊗φe₁ ⊕ c⊗φe₂)` —— 两个线性泛函在 `e₀/e₁/e₂` 上相等即处处相等。
-- 桥引理不可省：`a • e₀` 与 `(a,T₀,T₀)` 只是**命题**相等
--   （`a ⊗ T₁` / `a ⊗ T₀` 非定义性——`⊗` 按第一参数匹配）。
--------------------------------------------------------------------------------

-- 三个基向量（本模块自备，避免跨模块依赖）
e₀ e₁ e₂ : GF3Func
e₀ = T₁ , T₀ , T₀
e₁ = T₀ , T₁ , T₀
e₂ = T₀ , T₀ , T₁

decomp-f3 : ∀ a b c → (a , b , c) ≡ (a , T₀ , T₀) ⊕ₚ ((T₀ , b , T₀) ⊕ₚ (T₀ , T₀ , c))
decomp-f3 a b c =
  cong₂ (λ x y → (x , y , c)) (sym (⊕-identityʳ a)) (sym (⊕-identityʳ b))

•e₀≡ : ∀ a → a • e₀ ≡ (a , T₀ , T₀)
•e₀≡ a =
  trans (cong (λ z → (a ⊗ T₁ , a ⊗ T₀ , z)) (⊗-zeroʳ a))
        (cong₂ (λ x y → (x , y , T₀)) (⊗-identityʳ a) (⊗-zeroʳ a))

•e₁≡ : ∀ b → b • e₁ ≡ (T₀ , b , T₀)
•e₁≡ b =
  trans (cong (λ z → (z , b ⊗ T₁ , b ⊗ T₀)) (⊗-zeroʳ b))
        (cong₂ (λ x y → (T₀ , x , y)) (⊗-identityʳ b) (⊗-zeroʳ b))

•e₂≡ : ∀ c → c • e₂ ≡ (T₀ , T₀ , c)
•e₂≡ c =
  trans (cong (λ z → (z , c ⊗ T₀ , c ⊗ T₁)) (⊗-zeroʳ c))
        (trans (cong (λ z → (T₀ , z , c ⊗ T₁)) (⊗-zeroʳ c))
               (cong (λ z → (T₀ , T₀ , z)) (⊗-identityʳ c)))

-- 求值公式：`φ (a,b,c)` 由三个基值决定
φ-eval : ∀ (φ : Dual) → Linear φ → ∀ a b c
       → φ (a , b , c) ≡ ((a ⊗ φ e₀) ⊕ ((b ⊗ φ e₁) ⊕ (c ⊗ φ e₂)))
φ-eval φ (add , hom) a b c =
  trans (cong φ (decomp-f3 a b c))
        (trans (add (a , T₀ , T₀) ((T₀ , b , T₀) ⊕ₚ (T₀ , T₀ , c)))
               (cong₂ _⊕_ (trans (cong φ (sym (•e₀≡ a))) (hom a e₀))
                           (trans (add (T₀ , b , T₀) (T₀ , T₀ , c))
                                  (cong₂ _⊕_
                                         (trans (cong φ (sym (•e₁≡ b))) (hom b e₁))
                                         (trans (cong φ (sym (•e₂≡ c))) (hom c e₂))))))

linear-determined : ∀ (φ ψ : Dual) → Linear φ → Linear ψ
                  → φ e₀ ≡ ψ e₀ → φ e₁ ≡ ψ e₁ → φ e₂ ≡ ψ e₂
                  → ∀ f → φ f ≡ ψ f
linear-determined φ ψ lφ lψ e0 e1 e2 (a , b , c) =
  trans (φ-eval φ lφ a b c)
        (trans (cong₂ (λ p q → p ⊕ q)
                      (cong (a ⊗_) e0)
                      (cong₂ (λ p q → p ⊕ q) (cong (b ⊗_) e1) (cong (c ⊗_) e2)))
               (sym (φ-eval ψ lψ a b c)))

--------------------------------------------------------------------------------
-- §6. 维数定理的两条直接推论
--------------------------------------------------------------------------------

-- ① 在基上消失 ⇒ 恒为零（基的「非退化性」）
linear-zero : ∀ (φ : Dual) → Linear φ
            → φ e₀ ≡ T₀ → φ e₁ ≡ T₀ → φ e₂ ≡ T₀
            → ∀ f → φ f ≡ T₀
linear-zero φ lφ e0 e1 e2 f =
  linear-determined φ (λ _ → T₀) lφ ((λ _ _ → refl) , (λ k _ → sym (⊗-zeroʳ k))) e0 e1 e2 f

-- ② 基值相同 ⇒ 处处相同（求值映射在线性泛函上单射）
linear-eval-injective : ∀ (φ ψ : Dual) → Linear φ → Linear ψ
                      → φ e₀ ≡ ψ e₀ → φ e₁ ≡ ψ e₁ → φ e₂ ≡ ψ e₂
                      → ∀ f → φ f ≡ ψ f
linear-eval-injective = linear-determined
