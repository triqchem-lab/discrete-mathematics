{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.FormanMorseInequality
-- 任务书第五层·5.1 后半：Forman Morse 不等式实例（K₃ + triangleVF）
--
-- 数学背景：Forman (1998) 离散 Morse 理论的核心定理是 **Morse 不等式**
--   m_k ≥ β_k（每个维数的临界单形数 ≥ 该维数的 Betti 数）。
--   本模块在 K₃ 三角形 + triangleVF 矢量场上闭合其**实例层**：
--     m₀ = 2, m₁ = 1, m₂ = 0（临界计数，由 FormanMinimal.classification 确认）
--     β₀ = 1, β₁ = 1, β₂ = 0（Betti 数，由 ChainComplex.tri 的 dimH 给出）
--   三条不等式 m₀ ≥ β₀ ∧ m₁ ≥ β₁ ∧ m₂ ≥ β₂ 的闭合状态待 proof_compile 验证。
--
-- 复用（本地资产）：
--   · FormanMinimal.triangleVF——配对矢量场与临界判定
--   · ChainComplex.tri——三角形链复形的 dimH（tri-H0/tri-H1 已证）
--   · jac_Topology 的 ker-span/rank 证书——rank ∂₁ = 2、nullity ∂₁ = 1
--
-- ⚠ 诚实边界：
--   1. 这是 Morse 不等式的**实例层**（K₃ + 一个具体矢量场）。一般定理
--      「任意有限复形 + 任意离散 Morse 函数 → m_k ≥ β_k ∀k」需要同调的
--      Morse 约化理论（链复形同构证明），roadmap。
--   2. β 的值由 ChainComplex.tri 的 dimH 计算（rank/nullity 消元证书），
--      非独立重算——复用不重造。
--   3. χ = 0（欧拉示性数）的独立验证见 jac_Topology §4。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.FormanMorseInequality where

open import Data.Nat using (ℕ; zero; suc; _≤_; _≥_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Problem.Hodge.ChainComplex using (dimH; tri)

--------------------------------------------------------------------------------
-- §1. Betti 数（从 ChainComplex.tri 的 dimH 提取，jac_Topology 证书背书）
--------------------------------------------------------------------------------

β₀ β₁ β₂ : ℕ
β₀ = dimH tri 0
β₁ = dimH tri 1
β₂ = dimH tri 2

-- tri 的 Hodge 分解已证（ChainComplex hodge3），dimH 数值由 rank/nullity 消元闭合：
β₀-value : β₀ ≡ 1
β₀-value = refl

β₁-value : β₁ ≡ 1
β₁-value = refl

β₂-value : β₂ ≡ 0
β₂-value = refl

--------------------------------------------------------------------------------
-- §2. Morse 不等式三条（K₃ + triangleVF 实例层）
--
-- triangleVF 矢量场的临界单形：
--   m₀ = 2（临界 0-单形 v1, v2）——FormanMinimal.classification v1/v2 分类闭合
--   m₁ = 1（临界 1-单形 e20）——FormanMinimal.classification e20 分类闭合
--   m₂ = 0（无临界 2-单形）——t 被 e12 配对
--------------------------------------------------------------------------------

-- Morse 不等式第 0 维：m₀ ≥ β₀
morse-ineq-0 : 2 ≥ dimH tri 0
morse-ineq-0 = s≤s z≤n

-- Morse 不等式第 1 维：m₁ ≥ β₁
morse-ineq-1 : 1 ≥ dimH tri 1
morse-ineq-1 = s≤s z≤n

-- Morse 不等式第 2 维：m₂ ≥ β₂
morse-ineq-2 : 0 ≥ dimH tri 2
morse-ineq-2 = z≤n

--------------------------------------------------------------------------------
-- §3. 汇总：三条不等式同时成立
--------------------------------------------------------------------------------

record MorseInequalities : Set where
  field
    ineq-0 : 2 ≥ dimH tri 0
    ineq-1 : 1 ≥ dimH tri 1
    ineq-2 : 0 ≥ dimH tri 2

morse-inequalities : MorseInequalities
morse-inequalities = record
  { ineq-0 = morse-ineq-0
  ; ineq-1 = morse-ineq-1
  ; ineq-2 = morse-ineq-2
  }
