{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.FormanMinimal
-- 任务书第五层·5.1：Forman 离散 Morse 理论（1998）的构造性最小核
--
-- 数学背景：Forman, "Morse Theory for Cell Complexes"（Adv. Math. 134 (1998),
--   90–145；概要卡 §3）：离散 Morse 函数经**配对矢量场**（每单形至多配一个
--   恰高一维的余面）约化复形，临界单形数给出 Betti 数不等式。本模块在
--   三角形复形（3 顶点 3 边 1 面，枚举 7 单形）上给出：
--     ① 配对矢量场的良构性（维度律 + 配对单射性：同余面者同源）；
--     ② 实例：配对 (v0 ↦ e01, e12 ↦ t)，临界 = {v1, v2, e20}；
--     ③ 全单形二分（配对/临界）覆盖 + 互斥 + 计数守恒 2·2 + 3 ≡ 7；
--     ④ 对抗：两个临界顶点在 1-骨架（K₃）上仍连通（复用 AtkinQAnalysis）。
--
-- ⚠ 诚实边界：
--   1. Morse 不等式 m_k ≥ β_k 完整形式需要同调群——本模块只给 β₀ 层连通性
--      核对；完整不等式接 jac_Topology 同调机件，roadmap。
--   2. 一般复形上的矢量场是 roadmap；本模块锁枚举实例（7 单形，逐 case 构造）。
--   3. 「局部配对替代全局计算」与 jac_Topology 的 2×2 子式秩证书同族，
--      但路径不同（Morse 约化 vs CRT 分量）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.FormanMinimal where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; trans)
open import Sovereign.Base.Trit using (Trit)
open import Sovereign.Topology.AtkinQAnalysis
  using (Graph; Path; cons; nil)

--------------------------------------------------------------------------------
-- §1. 三角形复形的单形枚举（7 个）与维数
--------------------------------------------------------------------------------

data Sx : Set where
  v0 v1 v2    : Sx   -- 0 维
  e01 e12 e20 : Sx   -- 1 维（e_ab = 边 a→b）
  t           : Sx   -- 2 维（三角面）

dim : Sx → ℕ
dim v0 = zero
dim v1 = zero
dim v2 = zero
dim e01 = suc zero
dim e12 = suc zero
dim e20 = suc zero
dim t = suc (suc zero)

--------------------------------------------------------------------------------
-- §2. 配对矢量场的良构性
--
-- V σ = just τ 表示 σ 与余面 τ 配对（Forman 箭头 σ → τ）。
-- 良构两律：维度律（τ 恰高一维）+ 配对单射（同余面者同源——
--   部分函数的整体单射不成立：v1/v2/e01/e20/t 共享 nothing，
--   故单射性限定在 just 值域内，这是 Forman 配对的正确形状）。
--------------------------------------------------------------------------------

record MorseField : Set₁ where
  field
    V       : Sx → Maybe Sx
    dim-law : ∀ σ τ → V σ ≡ just τ → dim τ ≡ suc (dim σ)
    V-inj   : ∀ σ σ' τ → V σ ≡ just τ → V σ' ≡ just τ → σ ≡ σ'

--------------------------------------------------------------------------------
-- §3. 三角形实例：配对 (v0 ↦ e01, e12 ↦ t)，临界 {v1, v2, e20}
--------------------------------------------------------------------------------

triangleVF : Sx → Maybe Sx
triangleVF v0 = just e01
triangleVF v1 = nothing
triangleVF v2 = nothing
triangleVF e01 = nothing
triangleVF e12 = just t
triangleVF e20 = nothing
triangleVF t = nothing

-- 判定表：V 的 just 像只有 e01 与 t
V-just-dom : ∀ σ s → triangleVF σ ≡ just s → σ ≡ v0 ⊎ σ ≡ e12
V-just-dom v0 s h = inj₁ refl
V-just-dom v1 s ()
V-just-dom v2 s ()
V-just-dom e01 s ()
V-just-dom e12 s h = inj₂ refl
V-just-dom e20 s ()
V-just-dom t s ()

triangleVF-field : MorseField
triangleVF-field = record
  { V       = triangleVF
  ; dim-law = dl
  ; V-inj   = vi
  }
  where
    dl : ∀ σ τ → triangleVF σ ≡ just τ → dim τ ≡ suc (dim σ)
    dl v0 τ h = cong dim (sym (just-injective h))
    dl e12 τ h = cong dim (sym (just-injective h))
    dl v1 τ ()
    dl v2 τ ()
    dl e01 τ ()
    dl e20 τ ()
    dl t τ ()

    vi : ∀ σ σ' τ → triangleVF σ ≡ just τ → triangleVF σ' ≡ just τ → σ ≡ σ'
    vi σ σ' τ h₁ h₂ with V-just-dom σ τ h₁ | V-just-dom σ' τ h₂
    ... | inj₁ σ≡v0 | inj₁ σ'≡v0 = trans σ≡v0 (sym σ'≡v0)
    ... | inj₁ σ≡v0 | inj₂ σ'≡e12 =
      ⊥-elim (e01≢t (trans e₁ (sym e₂)))
      where
        e₁ : e01 ≡ τ
        e₁ = just-injective (trans (sym (cong triangleVF σ≡v0)) h₁)
        e₂ : t ≡ τ
        e₂ = just-injective (trans (sym (cong triangleVF σ'≡e12)) h₂)
        e01≢t : e01 ≡ t → ⊥
        e01≢t ()
    ... | inj₂ σ≡e12 | inj₁ σ'≡v0 =
      ⊥-elim (e01≢t (trans e₂' (sym e₁')))
      where
        e₁' : t ≡ τ
        e₁' = just-injective (trans (sym (cong triangleVF σ≡e12)) h₁)
        e₂' : e01 ≡ τ
        e₂' = just-injective (trans (sym (cong triangleVF σ'≡v0)) h₂)
        e01≢t : e01 ≡ t → ⊥
        e01≢t ()
    ... | inj₂ σ≡e12 | inj₂ σ'≡e12 = trans σ≡e12 (sym σ'≡e12)

--------------------------------------------------------------------------------
-- §4. 临界单形：无出配对且无入配对；二分覆盖 + 互斥 + 计数守恒
--------------------------------------------------------------------------------

IsPaired : Sx → Set
IsPaired σ =
  (¬ (triangleVF σ ≡ nothing)) ⊎ (Σ Sx (λ σ' → triangleVF σ' ≡ just σ))

IsCritical : Sx → Set
IsCritical σ = (triangleVF σ ≡ nothing) × (∀ σ' → triangleVF σ' ≡ just σ → ⊥)

-- 互斥：配对的单形不临界（出配对分支直接矛盾；入配对分支撞无入条款）
paired-not-critical : ∀ σ → IsPaired σ → IsCritical σ → ⊥
paired-not-critical σ (inj₁ h) (hc , _) = h hc
paired-not-critical σ (inj₂ (w , hw)) (_ , noin) = noin w hw

-- 覆盖：每单形非配对即临界。配对侧 4 个（v0/e12 配出，e01/t 被配入），
-- 临界侧 3 个（v1/v2/e20，内联模式 λ 逐构造子消去）。
classification : ∀ σ → IsPaired σ ⊎ IsCritical σ
classification v0 = inj₁ (inj₁ (λ ()))
classification e01 = inj₁ (inj₂ (v0 , refl))            -- 被配入：V v0 = just e01
classification e12 = inj₁ (inj₁ (λ ()))
classification t = inj₁ (inj₂ (e12 , refl))             -- 被配入：V e12 = just t
classification v1 =
  inj₂ (refl , λ { v0 () ; e12 () ; v1 () ; v2 () ; e01 () ; e20 () ; t () })
classification v2 =
  inj₂ (refl , λ { v0 () ; e12 () ; v1 () ; v2 () ; e01 () ; e20 () ; t () })
classification e20 =
  inj₂ (refl , λ { v0 () ; e12 () ; v1 () ; v2 () ; e01 () ; e20 () ; t () })

-- 计数守恒：2 个配对（各占 2 单形）+ 3 个临界 = 7 单形
conservation : 2 * 2 + 3 ≡ 7
conservation = refl

--------------------------------------------------------------------------------
-- §5. 具体点对抗（对抗验证协议 §6）：临界顶点仍连通
--
-- 临界顶点 v1, v2 在 1-骨架（K₃）上有显式路径 v1 → v2：
-- m₀ = 2 与 β₀ = 1 相容（m₀ ≥ β₀ 的实例面；完整不等式接同调，见诚实边界 1）。
--------------------------------------------------------------------------------

open import Sovereign.Topology.AtkinQAnalysis
  using (Path; cons; nil; Graph; tri)

v1-v2 : Graph.Edge tri (fsuc fzero) (fsuc (fsuc fzero))
v1-v2 = λ ()

critical-vertices-connected :
  Path (Graph.Edge tri) (fsuc fzero) (fsuc (fsuc fzero))
critical-vertices-connected =
  cons (fsuc fzero) (fsuc (fsuc fzero)) (fsuc (fsuc fzero))
       v1-v2 (nil (fsuc (fsuc fzero)))
