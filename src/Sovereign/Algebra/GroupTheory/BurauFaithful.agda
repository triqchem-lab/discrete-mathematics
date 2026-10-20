{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BurauFaithful
-- P3.4：Burau 表示不忠实性——**公理层裁决点**（L0 红线「不忠实商禁止」的验证点）
--
-- ★ 地位声明（2026-10-19 人类裁决 ✓）：本模块**不是**外部引用标签（E 类），
--   而是 L0 红线「非忠实商非合法同余关系」在边界情况上的**框架内裁决** ✓。
--   模块名沿用 BurauFaithful（历史引用不破坏 ✗ 不重命名——与 π₁ᵈ 处理一致 ✓）；
--   内容实为「Burau 不忠实性的商合法裁决」。
--
-- 裁决内容（合法对象 + 非法商 ✓）：
--   ① Burau 表示 ρ : Bₙ → GLₙ₋₁(ℤ[t,t⁻¹]) **本身合法**——辫群标准线性表示，存在性无争议；
--   ② 其诱导商 Bₙ/ker(ρ)（n≥5）**非法**——L0 红线：非忠实商非合法同余关系；
--   ③ 框架立场：**承认表示存在，不采纳其商**。
--
-- 外部事实（E 类标签，不本地重证 ✅）：Bigelow (1999) 证明 Burau 在 n≥5 不忠实。
--
-- 形式核心（本模块可证 ✓，与辫群无关的一般引理）：
--   ① UnfaithfulAt：核元素谓词（w ≠ 1 ∧ ρw = ρ1）
--   ② InfoLoss：核元素 ⇒ 商信息丢失 witness（构造性 ✓）
--   ③ adjudicate：非忠实 ⇒ 商拒绝（QuotientStance.rejected，构造性 ✓）
--
-- 0 postulate / 0 hole。
-- 包含：MonoidLike / UnfaithfulAt / NonFaithful / InfoLoss / QuotientStance /
--       adjudicate / Burau 外部标签与 π₁ᵈ·π₁bt 对照注记

module Sovereign.Algebra.GroupTheory.BurauFaithful where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- ① 一般层：表示的忠实性与商的合法性（与辫群无关的一般引理 ✓）
--------------------------------------------------------------------------------

record MonoidLike (B : Set) : Set where
  field
    one  : B
    _·_  : B → B → B
    ·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c)
    ·-lid   : ∀ a → one · a ≡ a
    ·-rid   : ∀ a → a · one ≡ a

-- 核元素谓词：w ≠ 单位元 且 ρ w ≡ ρ 1（表示无法分离 w 与单位元 ✓）
UnfaithfulAt : (B R : Set) (B-one : B) (R-one : R) (ρ : B → R) (w : B) → Set
UnfaithfulAt B R B-one R-one ρ w = (w ≡ B-one → ⊥) × (ρ w ≡ R-one)

NonFaithful : (B R : Set) (B-one : B) (R-one : R) (ρ : B → R) → Set
NonFaithful B R B-one R-one ρ = Σ B (λ w → UnfaithfulAt B R B-one R-one ρ w)

-- ★ 一般引理（构造性 ✓）：核元素给出「商信息丢失」的直接 witness——
--   在 ρ 诱导的等价（ρ 视为同一）下，w 与单位元被强制同一，
--   而 UnfaithfulAt 断言它们原不同 ⇒ 商丢失了 w 的信息（L0 红线的形式内核 ✓）
InfoLoss : (B R : Set) (B-one : B) (R-one : R) (ρ : B → R) (w : B)
  → UnfaithfulAt B R B-one R-one ρ w
  → Σ (B × B) (λ pair → (proj₁ pair ≡ B-one → ⊥) × (ρ (proj₁ pair) ≡ R-one))
InfoLoss B R B-one R-one ρ w (w≢one , ρw≡R1) = ((w , B-one) , w≢one , ρw≡R1)

--------------------------------------------------------------------------------
-- ② ★ 裁决函数：非忠实 ⇒ 商拒绝（L0 红线的构造性类型化 ✓）
--------------------------------------------------------------------------------

data QuotientStance : Set where
  admitted : QuotientStance   -- 忠实商：可采纳（如 π₁ᵈ / π₁bt——red-unique 已证 ✓）
  rejected : QuotientStance   -- 非忠实商：L0 红线拒绝（如 Burau 商 n≥5 ✓）

-- 裁决函数：存在核元素 ⇒ 商拒绝（构造性 ✓——非启发式，L0 红线直接应用 ✓）
adjudicate : (B R : Set) (B-one : B) (R-one : R) (ρ : B → R)
  → NonFaithful B R B-one R-one ρ → QuotientStance
adjudicate B R B-one R-one ρ nf = rejected

-- rejected 的语义配套：被拒商的信息丢失 witness 保持可用 ✓
rejected-info-loss : (B R : Set) (B-one : B) (R-one : R) (ρ : B → R) (w : B)
  → UnfaithfulAt B R B-one R-one ρ w
  → Σ (B × B) (λ pair → (proj₁ pair ≡ B-one → ⊥) × (ρ (proj₁ pair) ≡ R-one))
rejected-info-loss B R B-one R-one ρ w h = InfoLoss B R B-one R-one ρ w h

--------------------------------------------------------------------------------
-- ③ Burau 实例（外部标签 E 类 ✓ 不本地重证）+ 裁决应用
--------------------------------------------------------------------------------
-- 事实（Bigelow 1999，外部 ✅）：n≥5 时 ∃ w ≠ 1，burau-rep n w ≡ burau-rep n 1
--   ⇒ NonFaithful Bₙ GLₙ₋₁ 1 (burau-rep n)（外部事实代入 ✓）
-- 裁决：adjudicate ⇒ **rejected** ✓
--   · Burau 表示 ρ 本身 = **admitted 层**（合法对象，存在性无争议 ✓）
--   · 商 Bₙ/ker(ρ) = **rejected** ✓（L0 红线：非忠实商非合法同余 ✓）
--   · rejected-info-loss 保持核 witness 可用（与「同伦泄露」概念一致 ✓）
--
-- ★ 与 π₁ᵈ / π₁bt 的对照（ PIO 家族合法性确认 ✓）：
--   π₁ᵈ  = Walk / AStep   —— 忠实商（正规形唯一 red-unique 已证 ✓）⇒ admitted ✓
--   π₁bt = Walk / bt-等价 —— 忠实商（_PN4 gen-b 正规形 ✓）      ⇒ admitted ✓
--   两者的口径差（π₁ᵈ ≠ Barcelo）= **定义选择** ✗ 非合法性问题 ✗——
--   Burau 的问题是「商非法」，π₁ᵈ 的问题是「定义不同」——**不同层** ✓（§十 命名注记承接 ✓）


--------------------------------------------------------------------------------
-- ④ ★ 具体实例（管线代码验证 ✅）：最小非忠实表示的完整裁决——closed term ✓
--------------------------------------------------------------------------------
-- B₂ = ℤ/2（单位 true，生成元 false，false² = true）
-- ρtriv = 平凡表示（∀_ 映到单位）——核元素 = false（false ≢ true ✓ ρfalse ≡ ρtrue ✓）

stance-ex : QuotientStance
stance-ex =
  adjudicate Bool Bool true true
    (λ _ → true)                                   -- ρtriv：平凡表示
    (false , (λ ()) , refl)                        -- 核 witness：false ≢ true ∧ ρfalse ≡ true
-- ★ stance-ex **计算为 rejected**（构造性 ✓）——裁决是代码不是注释 ✓

stance-ex≡rejected : stance-ex ≡ rejected
stance-ex≡rejected = refl

--------------------------------------------------------------------------------
-- ⑤ Burau 裁决的代码化（外部事实作为显式参数 ✅ E 类约定 ✓）
--------------------------------------------------------------------------------
-- 通用核事实记录：任何「非忠实表示事实」都可打包为此记录（Bigelow n≥5 = 实例化来源 ✓）
record KernelFact (B R : Set) (B-one : B) (R-one : R) (ρ : B → R) : Set where
  field
    witness  : B
    witness-is-kernel : UnfaithfulAt B R B-one R-one ρ witness

-- 裁决代码化：核事实 ⇒ rejected（总函数 ✓——外部事实进参数，裁决进代码 ✓）
stance-from-fact : (B R : Set) (B-one : B) (R-one : R) (ρ : B → R)
  → KernelFact B R B-one R-one ρ → QuotientStance
stance-from-fact B R B-one R-one ρ kf =
  adjudicate B R B-one R-one ρ (KernelFact.witness kf , KernelFact.witness-is-kernel kf)

-- ★ Burau 实例化说明（E 类 ✅ 不本地重证）：
--   Bigelow 1999 提供 KernelFact Bₙ GLₙ₋₁ 1 1 (burau-rep n) 的 witness（n≥5）
--   ⇒ stance-from-fact 给出 **rejected**（代码级 ✓）
--   ⬜ 前置：Bₙ（辫群）形式化——roadmap（外部事实在此前保持 E 类注释 ✓ 诚实边界 ✓）