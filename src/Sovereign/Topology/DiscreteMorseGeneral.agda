{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.DiscreteMorseGeneral
-- 任务书第五层·5.1 泛型定义层：一般 K 上的离散 Morse 函数与临界复形
--
-- 对照任务书形式化切入点（原三个 stub 中的前两个）：
--   DiscreteMorseFunction : (K : CWComplex) → Set   ← 本模块 §1
--   criticalComplex : (f : DiscreteMorseFunction K) → ...  ← 本模块 §2
--   morse-inequality                                 ← 已实例层闭合
--
-- 展示群风格：载体 K 参数化（任意集合 + 维数函数），配对 record，
-- 临界谓词 data-free（¬×∀ 形态），临界复形 = Σ-类型过滤。
--
-- 诚实边界：泛型 Morse 同调定理（临界复合同调 ≅ 原同调，任意 f）
--   需代数 Morse 边界路由（交替路径），roadmap。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.DiscreteMorseGeneral where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)

open import Data.Nat.Properties using (suc-injective)

open import Sovereign.Topology.FormanMinimal as ᶠᵐ using (t)
tt≠v2 : ¬ (ᶠᵐ.t ≡ ᶠᵐ.v2)
tt≠v2 ()

n≢suc2 : ∀ (n : ℕ) → ¬ (n ≡ suc (suc n))
n≢suc2 zero ()
n≢suc2 (suc m) h = n≢suc2 m (suc-injective h)

--------------------------------------------------------------------------------
-- §1. DiscreteMorseFunction：一般 K 上的离散 Morse 函数
--   （任务书 stub ①；MorseField 的载体泛化——去 Sx 绑定）
--------------------------------------------------------------------------------

record DiscreteMorseFunction (K : Set) (dimK : K → ℕ) : Set₁ where
  field
    V       : K → Maybe K                          -- 配对箭头 σ ↦ τ
    dim-law : ∀ σ τ → V σ ≡ just τ → dimK τ ≡ suc (dimK σ)  -- 严格升维
    V-inj   : ∀ σ σ' τ → V σ ≡ just τ → V σ' ≡ just τ → σ ≡ σ'  -- 配对单射

--------------------------------------------------------------------------------
-- §2. 临界谓词与临界复形（任务书 stub ②）
--
--   IsCritical σ：σ 既非配对低端（V σ ≡ nothing）也非配对高端
--   （无 τ 使 V τ ≡ just σ）。
--   criticalComplex：临界单形的 Σ-类型过滤（按维数分层）。
--------------------------------------------------------------------------------

IsCritical : ∀ {K : Set} (dimK : K → ℕ) (V : K → Maybe K) (σ : K) → Set
IsCritical dimK V σ =
  (V σ ≡ nothing) × (¬ ∃-syntax (λ τ → V τ ≡ just σ))

-- 临界复形：k 维临界单形集合（Σ-类型过滤——泛型构造）
criticalComplex : ∀ {K : Set} (dimK : K → ℕ) (V : K → Maybe K) (k : ℕ) → Set
criticalComplex {K = K} dimK V k =
  Σ K (λ σ → (dimK σ ≡ k) × IsCritical dimK V σ)

--------------------------------------------------------------------------------
-- §3. 泛型无环性（MorseAcyclic 的定义层版本——维度律直接给无环）
--------------------------------------------------------------------------------

acyclic : ∀ {K : Set} (dimK : K → ℕ) (V : K → Maybe K) →
          (∀ σ τ → V σ ≡ just τ → dimK τ ≡ suc (dimK σ)) →
          ∀ σ τ → ¬ ((V σ ≡ just τ) × (V τ ≡ just σ))
acyclic dimK V dl σ τ (h₁ , h₂) = n≢suc2 (dimK τ) (trans dl₁ (cong suc dl₂))
  where
    dl₁ : dimK τ ≡ suc (dimK σ)
    dl₁ = dl σ τ h₁
    dl₂ : dimK σ ≡ suc (dimK τ)
    dl₂ = dl τ σ h₂

--------------------------------------------------------------------------------
-- §4. 临界性 → 非配对（临界单形不在任何配对中）
--------------------------------------------------------------------------------

critical-not-paired : ∀ {K : Set} (dimK : K → ℕ) (V : K → Maybe K) (σ : K) →
                      IsCritical dimK V σ → V σ ≡ nothing
critical-not-paired dimK V σ (hnothing , _) = hnothing

critical-not-upper : ∀ {K : Set} (dimK : K → ℕ) (V : K → Maybe K) (σ : K) →
                     IsCritical dimK V σ → ∀ τ → ¬ (V τ ≡ just σ)
critical-not-upper dimK V σ (_ , hupper) τ s = hupper (τ , s)

--------------------------------------------------------------------------------
-- §5. 实例对接：Sx 上的 MorseField 即 DiscreteMorseFunction Sx dim
--   （MorseField 的三字段与 DiscreteMorseFunction 的三字段逐一同型）
--------------------------------------------------------------------------------

open import Sovereign.Topology.FormanMinimal
  using (Sx; dim; v0; v1; v2; e01; e12; e20; t)
open import Sovereign.Topology.FormanPerfectField
  using (perfectVF; perfect-dim-law; e01≢v2; e12≢v2; t≢v2; nothing-just;
         e01≢e12; e01≢t; e12≢t)

V-inj-field : ∀ σ σ' τ → perfectVF σ ≡ just τ → perfectVF σ' ≡ just τ → σ ≡ σ'
V-inj-field v0 v0 e01 h₁ h₂ = refl
V-inj-field v1 v1 e12 h₁ h₂ = refl
V-inj-field e20 e20 t h₁ h₂ = refl
V-inj-field v2 σ' τ h₁ h₂ = ⊥-elim (nothing-just h₁)
V-inj-field e01 σ' τ h₁ h₂ = ⊥-elim (nothing-just h₁)
V-inj-field e12 σ' τ h₁ h₂ = ⊥-elim (nothing-just h₁)
V-inj-field t σ' τ h₁ h₂ = ⊥-elim (nothing-just h₁)
V-inj-field v0 σ' e12 h₁ h₂ = ⊥-elim (e01≢e12 (just-injective h₁))
V-inj-field v0 σ' t h₁ h₂ = ⊥-elim (e01≢t (just-injective h₁))
V-inj-field v0 v1 e01 h₁ h₂ = ⊥-elim (e01≢e12 (sym (just-injective h₂)))
V-inj-field v0 e20 e01 h₁ h₂ = ⊥-elim (e01≢t (sym (just-injective h₂)))
V-inj-field v0 v2 e01 h₁ h₂ = ⊥-elim (nothing-just h₂)
V-inj-field v0 e01 e01 h₁ h₂ = ⊥-elim (nothing-just h₂)
V-inj-field v0 e12 e01 h₁ h₂ = ⊥-elim (nothing-just h₂)
V-inj-field v0 t e01 h₁ h₂ = ⊥-elim (nothing-just h₂)
V-inj-field v1 σ' e01 h₁ h₂ = ⊥-elim (e01≢e12 (sym (just-injective h₁)))
V-inj-field v1 σ' t h₁ h₂ = ⊥-elim (e12≢t (just-injective h₁))
V-inj-field v1 v0 e12 h₁ h₂ = ⊥-elim (e01≢e12 (just-injective h₂))
V-inj-field v1 e20 e12 h₁ h₂ = ⊥-elim (e12≢t (sym (just-injective h₂)))
V-inj-field v1 v2 e12 h₁ h₂ = ⊥-elim (nothing-just h₂)
V-inj-field v1 e01 e12 h₁ h₂ = ⊥-elim (nothing-just h₂)
V-inj-field v1 e12 e12 h₁ h₂ = ⊥-elim (nothing-just h₂)
V-inj-field v1 t e12 h₁ h₂ = ⊥-elim (nothing-just h₂)
V-inj-field e20 σ' e01 h₁ h₂ = ⊥-elim (e01≢t (sym (just-injective h₁)))
V-inj-field e20 σ' e12 h₁ h₂ = ⊥-elim (e12≢t (sym (just-injective h₁)))
V-inj-field e20 v0 t h₁ h₂ = ⊥-elim (e01≢t (just-injective h₂))
V-inj-field e20 v1 t h₁ h₂ = ⊥-elim (e12≢t (just-injective h₂))
V-inj-field e20 v2 t h₁ h₂ = ⊥-elim (nothing-just h₂)
V-inj-field e20 e01 t h₁ h₂ = ⊥-elim (nothing-just h₂)
V-inj-field e20 e12 t h₁ h₂ = ⊥-elim (nothing-just h₂)
V-inj-field e20 t t h₁ h₂ = ⊥-elim (nothing-just h₂)

sx-perfect : DiscreteMorseFunction Sx dim
sx-perfect = record
  { V       = perfectVF
  ; dim-law = perfect-dim-law
  ; V-inj   = V-inj-field
  }


-- 完美场临界复形实例：0 维临界 = {v2}（1 个点）
crit0-v2 : criticalComplex dim perfectVF 0
crit0-v2 = v2 , (refl , (refl , nf))
  where
    nf : ¬ ∃-syntax (λ τ → perfectVF τ ≡ just v2)
    nf (τ , h) = aux τ h
      where
        aux : ∀ τ → perfectVF τ ≡ just v2 → ⊥
        aux v0 h = ⊥-elim (e01≢v2 (just-injective h))
        aux v1 h = ⊥-elim (e12≢v2 (just-injective h))
        aux v2 h = ⊥-elim (nothing-just h)
        aux e01 h = ⊥-elim (nothing-just h)
        aux e12 h = ⊥-elim (nothing-just h)
        aux e20 h = ⊥-elim (tt≠v2 (just-injective h))
        aux t h = ⊥-elim (nothing-just h)


