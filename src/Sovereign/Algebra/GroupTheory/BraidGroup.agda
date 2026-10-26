{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BraidGroup
-- P3.4 前置件：辫群 B_n 的最小形式化
--
-- 任务书 7.1：Burau 表示不忠实性（Bigelow 1999, n≥5）
-- 辫群 B_n 由 n-1 个生成元 σ₁,...,σ_{n-1} 满足：
--   ① σᵢσⱼ = σⱼσᵢ (|i-j| ≥ 2)
--   ② σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁
--
-- 本模块：B_3 的**展示 record**（2 个生成元 + 唯一关系 braid-rel）
-- ✅ 0 postulate / 0 hole（2026-10-26 复核：去注释后 `grep postulate` 无命中；agda EXIT=0）。
--   此前头部写「⚠ 2 个 postulate」是**陈旧声明**（2026-10-11 已由 record 字段化消除，注释未同步）。
-- ⚠ 诚实边界（这不是 postulate 问题，是另一件事）：本模块是**规范**不是**构造** ——
--   它陈述「凡满足这些字段的群即 B₃ 的候选模型」，既未构造出 B₃，也未证唯一性（泛性质）。
--   具体模型与 Burau 忠实性见文末 roadmap。
--
-- 核心原则：
--   1. 数学内容优先（背景→定义→引理→定理），证明每步可读；
--   2. 具名引理 + ∙/trans 链默认 ≤3 层；零洞零 postulate 目标；
--   3. 六段式分层：①头 ②导入 ③基础件 ④主引理 ⑤组合层 ⑥核对层。
--
-- 包含：record、module

module Sovereign.Algebra.GroupTheory.BraidGroup where

open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong)

-- B₃ = ⟨σ₁, σ₂ | σ₁σ₂σ₁ = σ₂σ₁σ₂⟩ 的**展示定义**
-- 数学背景：presentation 的关系**只有辫关系一条**（自由群上单关系）；逆元是群结构的
--   导出（σ₁⁻¹ = inv σ₁，σ₁·σ₁⁻¹ = e 由逆公理给出）——不是独立生成元、不是关系。
--   （2026-10-11 核实 2 修正：此前 σᵢ-inv 作关系 = 额外公理，与 B₃ 定义不符，已改导出定理。）
-- 结构分层：群结构字段（定义"群"，同 UniversalAlgebra.Group 口径）+ 生成元 σ₁/σ₂ + 唯一关系。
-- ──────────────────────────────────────────────
-- ③ 基础件层 / ④ 主引理层（具名引理，∙ 链 ≤3）
-- ──────────────────────────────────────────────
record B3 : Set₁ where
  field
    carrier : Set
    e       : carrier
    _·_     : carrier → carrier → carrier
    inv     : carrier → carrier
    σ₁ σ₂   : carrier
    -- 群结构（结构定义，非 presentation 关系）
    assoc     : ∀ x y z → (x · y) · z ≡ x · (y · z)
    identityˡ : ∀ x → e · x ≡ x
    identityʳ : ∀ x → x · e ≡ x
    inverseʳ  : ∀ x → x · inv x ≡ e
    -- 唯一 presentation 关系
    braid-rel : (σ₁ · (σ₂ · σ₁)) ≡ (σ₂ · (σ₁ · σ₂))

-- 逆律 = 导出定理（投影逆公理，零新公理）
module _ (G : B3) where

-- ──────────────────────────────────────────────
-- ⑤ 组合层（主定理/装配收口）
-- ──────────────────────────────────────────────
  open B3 G
  σ₁-inv : σ₁ · inv σ₁ ≡ e
  σ₁-inv = inverseʳ σ₁
  σ₂-inv : σ₂ · inv σ₂ ≡ e
  σ₂-inv = inverseʳ σ₂

  -- 单位元唯一：由字段推出的**定理**（不是字段访问），用以说明 record 不是空壳。
  -- 证：x ≡ x·e（identityʳ 的对称）≡ e（把 x·y≡y 用 y:=e）。
  e-unique : ∀ (x : carrier) → (∀ y → x · y ≡ y) → x ≡ e
  e-unique x left = trans (sym (identityʳ x)) (left e)

  -- ──────────────────────────────────────────────────────────────────────
  -- ⑥ 中心性：Δ² = (σ₁σ₂)³ 与两个生成元交换
  --
  -- 这是 B₃ 的第一个**非平凡定理**（不是字段访问，只用 assoc + braid-rel，
  -- **不用逆元**）。数学内容：Δ = σ₁σ₂σ₁ 是半扭转（half-twist），
  -- Δ² 生成 B₃ 的中心 Z(B₃) ≅ ℤ；在 2A₄ ≅ SL(2,F₃) 的像里 Δ² ↦ −I。
  -- 推导（a=σ₁, b=σ₂, 并置右结合；R: aba ≡ bab）：
  --   aΔ = a·(a·(b·a)) ≡ a·(b·(a·b))        [cong (a ·_) R]
  --   Δb = (a·(b·a))·b ≡ a·((b·a)·b) ≡ a·(b·(a·b))   [assoc]
  --   ⇒ aΔ ≡ Δb；同法 bΔ ≡ Δa。
  --   a·Δ² ≡ (aΔ)Δ ≡ (Δb)Δ ≡ Δ(bΔ) ≡ Δ(Δa) ≡ Δ²a。
  -- ──────────────────────────────────────────────────────────────────────
  Δ : carrier
  Δ = σ₁ · (σ₂ · σ₁)

  -- σ₁·Δ ≡ Δ·σ₂（左乘 σ₁ 换成右乘 σ₂）
  σ₁-Δ : σ₁ · Δ ≡ Δ · σ₂
  σ₁-Δ =
    trans (cong (σ₁ ·_) braid-rel)
      (sym (trans (assoc σ₁ (σ₂ · σ₁) σ₂)
                  (cong (σ₁ ·_) (assoc σ₂ σ₁ σ₂))))

  -- σ₂·Δ ≡ Δ·σ₁（反向交换）
  σ₂-Δ : σ₂ · Δ ≡ Δ · σ₁
  σ₂-Δ =
    sym (trans (cong (_· σ₁) braid-rel)
          (trans (assoc σ₂ (σ₁ · σ₂) σ₁)
                 (cong (σ₂ ·_) (assoc σ₁ σ₂ σ₁))))

  -- Δ² 与 σ₁ 交换
  Δ²-central-σ₁ : σ₁ · (Δ · Δ) ≡ (Δ · Δ) · σ₁
  Δ²-central-σ₁ =
    trans (sym (assoc σ₁ Δ Δ))
      (trans (cong (_· Δ) σ₁-Δ)
        (trans (assoc Δ σ₂ Δ)
          (trans (cong (Δ ·_) σ₂-Δ)
                 (sym (assoc Δ Δ σ₁)))))

  -- Δ² 与 σ₂ 交换
  Δ²-central-σ₂ : σ₂ · (Δ · Δ) ≡ (Δ · Δ) · σ₂
  Δ²-central-σ₂ =
    trans (sym (assoc σ₂ Δ Δ))
      (trans (cong (_· Δ) σ₂-Δ)
        (trans (assoc Δ σ₁ Δ)
          (trans (cong (Δ ·_) σ₁-Δ)
                 (sym (assoc Δ Δ σ₂)))))

  -- ── 与用户口径对齐：(σ₁σ₂)³ 的中心性 ─────────────────────────────
  -- Δ² = (σ₁σ₂)³ 是两个**不同的词**（aba·aba vs ababab），其等式需单独证；
  -- 否则「Δ² 中心」不等于「(σ₁σ₂)³ 中心」。下面的桥接是关键一步。

  W : carrier          -- (σ₁σ₂)³
  W = σ₁ · (σ₂ · (σ₁ · (σ₂ · (σ₁ · σ₂))))

  -- Δ·Δ ≡ W：由 braid-rel 把右因子 a·(b·a) 换成 b·(a·b)，再重新结合
  Δ²-is-W : (Δ · Δ) ≡ W
  Δ²-is-W =
    trans (cong (Δ ·_) braid-rel)
      (trans (assoc σ₁ (σ₂ · σ₁) (σ₂ · (σ₁ · σ₂)))
             (cong (σ₁ ·_) (assoc σ₂ σ₁ (σ₂ · (σ₁ · σ₂)))))

  -- **主定理**：(σ₁σ₂)³ 与 σ₁ 交换
  W-central-σ₁ : σ₁ · W ≡ W · σ₁
  W-central-σ₁ =
    trans (cong (σ₁ ·_) (sym Δ²-is-W))
      (trans Δ²-central-σ₁ (cong (_· σ₁) Δ²-is-W))

  -- **主定理**：(σ₁σ₂)³ 与 σ₂ 交换
  W-central-σ₂ : σ₂ · W ≡ W · σ₂
  W-central-σ₂ =
    trans (cong (σ₂ ·_) (sym Δ²-is-W))
      (trans Δ²-central-σ₂ (cong (_· σ₂) Δ²-is-W))



-- 诚实边界：B₃ 唯一性（泛性质：任意群 + 满足辫关系的两元素 → 唯一同态）与
--   Burau 表示实例留 roadmap。本模块交付：关系入定义的展示形态（3 postulate → 0）。
-- Burau 表示声明（roadmap）
-- burau-rep : B3 → GL₂(Z[t,t⁻¹])
-- burau-rep σ₁ = [[1-t, t], [1, 0]]
-- burau-rep σ₂ = [[1, 0], [t⁻¹, 1-t⁻¹]]
-- burau-faithful : ¬ (Injective burau-rep)  -- Bigelow 1999
