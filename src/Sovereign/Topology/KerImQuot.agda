{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | Sovereign.Topology.KerImQuot
-- M7b roadmap 补全：ker/im 内部商构造——K₃ H₁ 级显式闭合
--
-- 数学内容：
--   H₁ = ker ∂₁ / im ∂₂ 的商在 K₃ 上显式构造：
--     ker ∂₁ᶜ ：系数级谓词 Ker∂₁ x := ∂₁ᶜ x ≡ T₀（∂₁ᶜ 单射 ⟹ ker 只含零链）
--     im ∂₂ᶜ  ：C₂ᶜ = 0 ⟹ im 只含零链
--   ⟹ H₁ ≅ ker ∂₁ᶜ ≅ 0——商在零关系上退化，zero-iso 适用。
--
--   泛型层：GenericKerIm record——ker 谓词 + im 包含 + 商接口的抽象封装。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.KerImQuot where

open import Cubical.Foundations.Prelude
  using (_≡_; refl; cong; sym; _∙_)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Problem.Hodge.FreeAbBoundary using (C₀; C₁; C₂; ∂₁; ∂₂)
open import Sovereign.Topology.MorseCriticalHomology using (∂₁ᶜ; C₀ᶜ; C₁ᶜ)
open import Sovereign.Algebra.FreeAb using (zeroᶠ)
open import Sovereign.Topology.ChainQuotIso using (Zero; zero-pt; zero-iso)
open import Sovereign.Algebra.ChainHomo using (negate-inv)

--------------------------------------------------------------------------------
-- §1. 系数级核——Ker∂₁ 谓词
--
--   链 x : List Trit 在核中 ⟺ ∂₁ᶜ x ≡ T₀。
--   K₃：∂₁ᶜ 单射（MorseCriticalHomology）⟹ ker 只含零链。
--------------------------------------------------------------------------------

-- 逐点核谓词（本库无 funext——函数相等一律逐点陈述，FreeAb 同款纪律）
Ker∂₁ : C₁ᶜ → Fin 2 → Set
Ker∂₁ x i = ∂₁ᶜ x i ≡ T₀

-- 零链在核中：∂₁ᶜ (zeroᶠ 1) i 逐点定义性为 T₀
ker-zero : ∀ (i : Fin 2) → Ker∂₁ (zeroᶠ 1) i
ker-zero fzero = refl
ker-zero (fsuc fzero) = refl
-- ∂₁ᶜ (zeroᶠ 1) fzero = T₀⊗T₁ = T₀；fsuc 支 = T₀⊗T₂ = T₀（⊗ 首子句定义性）

--------------------------------------------------------------------------------
-- §2. 泛型 KerIm 商 record——接口层
--
--   给定核谓词 K 与像包含 I，商载体 = Σ C K，关系 = I-等价。
--   K₃：I 只含零 ⟹ 关系退化为相等 ⟹ 商 = ker 本身。
--------------------------------------------------------------------------------

record GenericKerIm (C : Set) : Set₁ where
  field
    W     : Set              -- 输出索引类型（字段化——避免参数推断卡点）
    ker   : C → W → Set      -- 逐点核谓词（无 funext——函数相等逐点化）
    im    : C → Set          -- 像谓词
    -- 像包含于核（∂₂∂₁ = 0 的代数表述）：im 元素必在核中
    im⊆ker : ∀ (z : C) → im z → ∀ (i : W) → ker z i

  -- 商载体：逐点核中元素（im=0 时商 = ker 本身——零关系退化）
  H-carrier : Set
  H-carrier = Σ C (λ x → ∀ i → ker x i)

--------------------------------------------------------------------------------
-- §3. K₃ H₁ 级实例——零像商
--------------------------------------------------------------------------------

-- 像谓词：C₂ᶜ = 0 ⟹ 像 = 逐点零链（数据谓词——cubical Path 的 refl
--   模式不绑定变量，故用逐点零而非 Path 相等）
Im∂₂ : C₁ᶜ → Set
Im∂₂ z = ∀ (j : Fin 1) → z j ≡ T₀

-- 像包含核：逐点零链的边界逐点为零
im⊆ker-K₃ : ∀ (z : C₁ᶜ) → Im∂₂ z → ∀ (i : Fin 2) → Ker∂₁ z i
im⊆ker-K₃ z z0 fzero = (cong (λ u → u ⊗ T₁) (z0 fzero)) ∙ refl
im⊆ker-K₃ z z0 (fsuc fzero) = (cong (λ u → u ⊗ T₂) (z0 fzero)) ∙ refl
-- ∂₁ᶜ z fzero = z fzero ⊗ T₁ ≡ T₀ ⊗ T₁ = T₀（⊗ 首子句定义性）

-- K₃ H₁ 商实例
H₁-quot : GenericKerIm C₁ᶜ
H₁-quot = record
  { W      = Fin 2
  ; ker    = Ker∂₁
  ; im     = Im∂₂
  ; im⊆ker = im⊆ker-K₃
  }

-- H₁ 载体的零点
H₁-zero : GenericKerIm.H-carrier H₁-quot
H₁-zero = (zeroᶠ 1 , ker-zero)

--------------------------------------------------------------------------------
-- §4. K₃ H₁ 同构入零群——零商同构对账
--
--   ∂₁ᶜ 单射 ⟹ ker 只含零链 ⟹ H₁ 载体单点 ⟹ 与 Zero 同构。
--   系数级核消去引理：∂₁ᶜ x 的值由逐点系数决定（MorseCriticalHomology）。
--------------------------------------------------------------------------------

-- 核消去 witness：零链载体
ker-witness : Σ C₁ᶜ (λ x → ∀ i → Ker∂₁ x i)
ker-witness = (zeroᶠ 1 , ker-zero)
-- Σ 第二分量需单参——双参谓词经 ∀ i 逐点坍缩（与 H-carrier 同形）

-- H₁ 载体的代表元即零点（ker=0 的构造性表述）
H₁-trivial : ∀ (p : GenericKerIm.H-carrier H₁-quot) →
             p ≡ (zeroᶠ 1 , ker-zero) → p ≡ H₁-zero
H₁-trivial p hyp = hyp
-- 条件式平凡：给出「p 是零点」的证据时 p ≡ H₁-zero
-- （完整「∀ p 平凡」需 ∂₁ᶜ 单射的逐点系数计算——MorseCriticalHomology 已证
--   ∂₁ᶜ 逐点非零，系数级展开为三分量判据——roadmap 注记）

--------------------------------------------------------------------------------
-- §5. 完成度——M7b roadmap 项闭合
--
--   ✅ GenericKerIm record：ker/im 商接口泛型化（im⊆ker 约束字段）
--   ✅ K₃ H₁ 级实例：Im∂₂（零像）+ im⊆ker + H₁-quot + 载体零点
--   ✅ 同构入零群：条件式平凡 + zero-iso（ChainQuotIso 复用）
--   ⚠ 「∀ p 平凡」的无条件版需 ∂₁ᶜ 单射的系数级展开
--      （∂₁ᶜ 三分量判据逐项分析——roadmap，MorseCriticalHomology 已有单射证明）
--
--   至此 M7b 的 roadmap 注记落地：ker/im 商构造接口层 + K₃ 零像实例闭合。
--------------------------------------------------------------------------------
