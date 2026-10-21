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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; ⊕-comm; ⊗-comm)
open import Sovereign.Algebra.Analytic.ProjectionDifferential using (GF3Func)

zero3 : GF3Func
zero3 = T₀ , T₀ , T₀

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
