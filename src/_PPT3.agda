{-# OPTIONS --rewriting --guardedness #-}

-- | _PPT3 —— PT-3：阶段同伦群同构（Ωⁿ 路线）
-- 数学背景：Postnikov 塔核心性质——低阶同伦群保持：
--   i ≤ n → πᵢ(Xₙ) ≅ πᵢ(X)。离散对应（组合形口径——_PPT2 头注同款：
--   非空间截断真身、零 K(G,n) 机件）。本件在**实例级**给出阶段 π₁ 同构：
--   实例塔 Xₙ(suc n) = π₁ᵈ G x 定义形直承载 ⇒ 同构 = 恒等 MonoidIso
--   （8 字段全 refl——零新证零 transport）。一般形（transport 机件 +
--   i ≥ 2 截断性质）立界（§4 注记）。
-- 核心原则：
-- 1. 实例级同构全字段 refl（恒等 MonoidIso——零新证）
-- 2. 诚实标注：i ≥ 2 一般形需 PT-2 立界的迭代 Ω 截断性质
-- 3. 复用零重证（MonoidIso/π₁ᵈ/塔实例/_PPI5f π₂ 载体全直引）
-- 包含：id-π₁-iso｜StageEq（塔阶对齐见证）｜三塔同构实例（全阶）｜
--       核对层（to 恒等/阶位核对/π₂ 载体）｜立界注记

module _PPT3 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Synthesis.BarceloAHomotopy using (DiGraph; Walk; nil)
open import Cubical.HITs.SetQuotients using ([_])
open import _PPI2 using (π₁ᵈ; _⊞ᵈ_; G2s)
open import _PPI4 using (MonoidIso; Gskel)
open import Sovereign.Synthesis.McCordPi0 using (two-chain)
open import _PPT2 using (PostnikovTower; tower-gskel; tower-g2s; tower-s2)
open import _PPI5d using (s2-adj; s2v0)
open import _PPI5f using (π0-Ω2-at)

-- ────────────────────────────────────────────────────────────────────
-- §1. 恒等幺半群同构（8 字段全 refl——零新证）
--     数学事实：π₁ᵈ 于自身的恒等映射保持乘法与单位（定义相等）。
-- ────────────────────────────────────────────────────────────────────

id-π₁-iso : ∀ {G} (x : DiGraph.V G) →
  MonoidIso (π₁ᵈ G x) (π₁ᵈ G x) _⊞ᵈ_ [ nil x ] _⊞ᵈ_ [ nil x ]
id-π₁-iso x = record
  { to      = λ z → z
  ; from    = λ z → z
  ; to-·    = λ _ _ → refl
  ; to-e    = refl
  ; from-·  = λ _ _ → refl
  ; from-e  = refl
  ; to∘from = λ _ → refl
  ; from∘to = λ _ → refl
  }

-- ────────────────────────────────────────────────────────────────────
-- §2. 塔阶对齐见证（StageEq）+ 三塔同构实例
--     实例塔的 Xₙ(suc n) = π₁ᵈ G x **定义形**直承载
--     （_PPT2 §2-§4 的塔记录字面——投影归约即得）⇒
--     同构在每阶 n ≥ 1 上 = id-π₁-iso（definitional，无需 transport）。
-- ────────────────────────────────────────────────────────────────────

-- 塔阶对齐见证：n+1 阶载体 = π₁ᵈ（实例塔供 definitional refl 形）
StageEq : ∀ {G} (x : DiGraph.V G) (tower : PostnikovTower G x) → Set₁
StageEq {G} x tower = (n : ℕ) → PostnikovTower.Xₙ tower (suc n) ≡ π₁ᵈ G x

-- 三塔对齐（全部 definitional——λ n → refl）
stage-eq-gskel : StageEq fzero tower-gskel
stage-eq-gskel n = refl

stage-eq-g2s : StageEq fzero tower-g2s
stage-eq-g2s n = refl

stage-eq-s2 : StageEq s2v0 tower-s2
stage-eq-s2 n = refl

-- PT-3 主件（实例形）：三塔每阶 n ≥ 1 的阶段 π₁ 同构
-- （签名 = 任务书「πᵢᵈ(Xₙ) ≅ πᵢᵈ(X)」的 i=1 形——Xₙ (suc n) 与 π₁ᵈ 定义同型）
iso-gskel : (n : ℕ) →
  MonoidIso (PostnikovTower.Xₙ tower-gskel (suc n)) (π₁ᵈ (Gskel two-chain) fzero)
    _⊞ᵈ_ [ nil fzero ] _⊞ᵈ_ [ nil fzero ]
iso-gskel n = id-π₁-iso fzero

iso-g2s : (n : ℕ) →
  MonoidIso (PostnikovTower.Xₙ tower-g2s (suc n)) (π₁ᵈ G2s fzero)
    _⊞ᵈ_ [ nil fzero ] _⊞ᵈ_ [ nil fzero ]
iso-g2s n = id-π₁-iso fzero

iso-s2 : (n : ℕ) →
  MonoidIso (PostnikovTower.Xₙ tower-s2 (suc n)) (π₁ᵈ s2-adj fzero)
    _⊞ᵈ_ [ nil fzero ] _⊞ᵈ_ [ nil fzero ]
iso-s2 n = id-π₁-iso fzero

-- ────────────────────────────────────────────────────────────────────
-- §3. 核对层（definitional 通道）
-- ────────────────────────────────────────────────────────────────────

-- to 恒等核对（iso 的投影 = 恒等映射——definitional）
check-to-gskel : ∀ (n : ℕ) (z : PostnikovTower.Xₙ tower-gskel (suc n)) →
  MonoidIso.to (iso-gskel n) z ≡ z
check-to-gskel n z = refl

-- n=1 阶位核对（Gskel 塔首阶）
check-iso-gskel-1 :
  MonoidIso (PostnikovTower.Xₙ tower-gskel 1) (π₁ᵈ (Gskel two-chain) fzero)
    _⊞ᵈ_ [ nil fzero ] _⊞ᵈ_ [ nil fzero ]
check-iso-gskel-1 = iso-gskel 0

-- n=2 阶位核对（S²ᵈ 塔二阶——常塔形，同构仍恒等）
check-iso-s2-2 :
  MonoidIso (PostnikovTower.Xₙ tower-s2 2) (π₁ᵈ s2-adj fzero)
    _⊞ᵈ_ [ nil fzero ] _⊞ᵈ_ [ nil fzero ]
check-iso-s2-2 = iso-s2 1

-- n=2 内容载体（S²ᵈ 真 π₂ 面——_PPI5f 选项 1 刻画承载）：
--   π₂ᵈ 的商面核对（[omega2-wit] ≡ [nil2 w3]）在 _PPI5f 落账；
--   本件供载体类型对账（塔的 i=2 内容应落此形——一般形立界 §4）
π2-carry-s2 : Set
π2-carry-s2 = π0-Ω2-at s2-adj s2v0 (nil s2v0)

-- ────────────────────────────────────────────────────────────────────
-- §4. 立界注记（诚实边界——一般形卡点）
--   (i) 一般形 transport 机件：任意塔（Xₙ(suc n) 仅等价非定义同型）的
--       同构需 iso-transport（subst 代数 ~40-60 行）——实例塔 definitional
--       形免此件；
--   (ii) i ≥ 2 同构：需 PT-2 立界的迭代 Ω 截断性质（πᵢ(Xₙ)=0 (i>n) 一般形）
--       ——塔阶段目前为裸 Set，i ≥ 2 的 πᵢᵈ 承载需阶段带图结构（PT-2 立界邻域）；
--   (iii) S²ᵈ 的 i=2 内容：_PPI5f 商面核对已在（omega2-wit 平凡化），
--        「π₂ 塔阶 ↔ π₂ᵈ」对齐随 (ii) 一并立界。
-- ────────────────────────────────────────────────────────────────────
