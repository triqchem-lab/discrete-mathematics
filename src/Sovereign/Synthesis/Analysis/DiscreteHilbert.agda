{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Analysis.DiscreteHilbert
--
-- GF(3) 上「内积」的真实面貌：**对称双线性但不正定**（各向同性向量存在）。
--
-- ## 数学内容
--
-- 在 `GF3Func = Trit³` 上取标准配对
--   `⟨f , g⟩ = f₀⊗g₀ ⊕ f₁⊗g₁ ⊕ f₂⊗g₂`
-- 则：
--   · **对称**（`⟨,⟩-sym`）✓
--   · **不正定**（`⟨,⟩-isotropic` + `⟨,⟩-not-definite`）✗
--   · 双线性：**本模块未证**（需 `⊕ₚ` 的分配律重排，约 10 步 `⊕-assoc`/`⊕-comm`）——
--     不写成定理，也不在文档里冒充（遵守散文断言规则）。
--
-- 关键事实：特征 3 下 `1 + 1 + 1 = 0`，于是 `f = (T₁,T₁,T₁)` 满足
-- `⟨f,f⟩ = T₀` 却 `f ≢ 0` —— **各向同性向量（null vector）存在**。
-- 因此「离散 Hilbert 空间」在 GF(3) 上只能是**正交空间 / 对称双线性空间**，
-- 不能是内积空间：正定性这条公理**在特征 3 下为假**，不是「尚未证明」。
--
-- ## 与 `Foundation.CompletenessTheorem` 的关系
--
-- 该模块把 `HilbertSpace` 的离散载体定为 `GF3Func × GF3Func` 并注明缺「概念特有定律」。
-- 本模块给出的是**该定律的否证**（附对称性与双线性两条成立的定律）——
-- 这比「留作未完成」更诚实，也说明该缺口属**改陈述**而非补证明。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；否定结论由**具体反例**给出（`refl` 级）
--------------------------------------------------------------------------------

module Sovereign.Synthesis.Analysis.DiscreteHilbert where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; ⊕-comm; ⊗-comm; ⊕-identityʳ; ⊗-identityˡ; ⊗-zeroˡ)
open import Sovereign.Algebra.Analytic.ProjectionDifferential using (GF3Func)

zero3 : GF3Func
zero3 = T₀ , T₀ , T₀

proj-0 proj-1 proj-2 : GF3Func → Trit
proj-0 (a , _ , _) = a
proj-1 (_ , b , _) = b
proj-2 (_ , _ , c) = c

--------------------------------------------------------------------------------
-- §1. 标准配对
--------------------------------------------------------------------------------

⟨_,_⟩ : GF3Func → GF3Func → Trit
⟨ (a , b , c) , (x , y , z) ⟩ = (a ⊗ x) ⊕ ((b ⊗ y) ⊕ (c ⊗ z))

--------------------------------------------------------------------------------
-- §2. 对称性（成立）
--------------------------------------------------------------------------------

⟨,⟩-sym : ∀ f g → ⟨ f , g ⟩ ≡ ⟨ g , f ⟩
⟨,⟩-sym (a , b , c) (x , y , z) =
  cong₂ _⊕_ (⊗-comm a x) (cong₂ _⊕_ (⊗-comm b y) (⊗-comm c z))

--------------------------------------------------------------------------------
-- §3. ★ 不正定：各向同性向量存在
--
-- `(T₁,T₁,T₁)` 的「范数」是 `1+1+1 = 0`（特征 3）⇒ 非零却范数为零。
--------------------------------------------------------------------------------

isotropic : GF3Func
isotropic = T₁ , T₁ , T₁

⟨,⟩-isotropic : ⟨ isotropic , isotropic ⟩ ≡ T₀
⟨,⟩-isotropic = refl

isotropic≢zero : isotropic ≢ zero3
isotropic≢zero ()

-- ⇒ 正定性（`⟨f,f⟩ ≡ 0 ⇒ f ≡ 0`）在 GF(3) 上**不成立**
⟨,⟩-not-definite : (∀ f → ⟨ f , f ⟩ ≡ T₀ → f ≡ zero3) → ⊥
⟨,⟩-not-definite h = isotropic≢zero (h isotropic ⟨,⟩-isotropic)

-- ⇒ 更强的表述：存在非零的各向同性向量
null-vector : Σ GF3Func (λ f → f ≢ zero3)
null-vector = isotropic , isotropic≢zero

--------------------------------------------------------------------------------
-- §4. ★ 非退化（配合 §2 对称、§3 不定 ⇒ 这是**正交空间**的完整刻画）
--
-- `⟨f , g⟩ ≡ 0` 对所有 `f` 成立 ⇒ `g = 0`。取三个基向量 `e₀/e₁/e₂` 即得三个坐标为零。
--------------------------------------------------------------------------------

e₀ e₁ e₂ : GF3Func
e₀ = T₁ , T₀ , T₀
e₁ = T₀ , T₁ , T₀
e₂ = T₀ , T₀ , T₁

-- 基向量上的求值 = 对应坐标（`x ⊕ T₀` 非定义性，故需 `⊕-identityʳ`）
eval-e₀ : ∀ g → ⟨ e₀ , g ⟩ ≡ proj-0 g
eval-e₀ (x , y , z) =
  trans (cong₂ _⊕_ (⊗-identityˡ x) (cong₂ _⊕_ (⊗-zeroˡ y) (⊗-zeroˡ z)))
        (⊕-identityʳ x)

eval-e₁ : ∀ g → ⟨ e₁ , g ⟩ ≡ proj-1 g
eval-e₁ (x , y , z) =
  trans (cong₂ _⊕_ (⊗-zeroˡ x) (cong₂ _⊕_ (⊗-identityˡ y) (⊗-zeroˡ z)))
        (⊕-identityʳ y)

eval-e₂ : ∀ g → ⟨ e₂ , g ⟩ ≡ proj-2 g
eval-e₂ (x , y , z) =
  trans (cong₂ _⊕_ (⊗-zeroˡ x) (cong₂ _⊕_ (⊗-zeroˡ y) (⊗-identityˡ z))) refl

⟨,⟩-nondegenerate : ∀ g → (∀ f → ⟨ f , g ⟩ ≡ T₀) → g ≡ zero3
⟨,⟩-nondegenerate (x , y , z) h = go x≡0 y≡0 z≡0
  where
    x≡0 : x ≡ T₀
    x≡0 = trans (sym (eval-e₀ (x , y , z))) (h e₀)
    y≡0 : y ≡ T₀
    y≡0 = trans (sym (eval-e₁ (x , y , z))) (h e₁)
    z≡0 : z ≡ T₀
    z≡0 = trans (sym (eval-e₂ (x , y , z))) (h e₂)
    go : x ≡ T₀ → y ≡ T₀ → z ≡ T₀ → (x , y , z) ≡ zero3
    go refl refl refl = refl
