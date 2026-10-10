{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.FaddeevYangBaxter
-- 任务书 6.3：Faddeev-Reshetikhin 构造核心——Yang-Baxter 解诱导 braid 关系
--
-- 数学背景：Faddeev-Reshetikhin 挫从 YB 算子（R-矩阵）构造纽结不变量——
--   核心一步：YB 解诱导 B₃ 表示（σ₁ = R₁₂、σ₂ = R₂₃）——
--   braid 关系 σ₁σ₂σ₁ = σ₂σ₁σ₂ 恰为 braid-YB 方程。
--
-- 核心原则：
-- 1. 纯构造（record + 乘积投影 + with 形——零 mod-helper 零 literal 归纳）
-- 2. 诚实边界：Faddeev-Reshetikhin 真身是量子群/纽结多项式——本层为 braid 诱导核心
-- 3. 与 Burau 线衔接（BurauCubical 的 braid-rel 是 R-矩阵实例代数侧）
--
-- 包含：R₁₂/R₂₃ 三元组算子 / YBSolution（braid-YB 方程）/ braid-rep 诱导引理

module Sovereign.Algebra.FaddeevYangBaxter where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- ────────────────────────────────────────────────────────────────────
-- §1. Yang-Baxter 算子（set-theoretic solution）+ braid-YB 方程
-- ────────────────────────────────────────────────────────────────────

record YBSolution (A : Set) : Set₁ where
  field
    R : A → A → A × A

open YBSolution

-- 三元组算子（R 在 (1,2)/(2,3) 分量的作用——B₃ 嵌入）
R₁₂ : {A : Set} → YBSolution A → A × A × A → A × A × A
R₁₂ S (x , y , z) with R S x y
... | (x' , y') = x' , y' , z

R₂₃ : {A : Set} → YBSolution A → A × A × A → A × A × A
R₂₃ S (x , y , z) with R S y z
... | (y' , z') = x , y' , z'

-- σ 嵌入（Faddeev 诱导）
σ₁-act : {A : Set} → YBSolution A → A × A × A → A × A × A
σ₁-act = R₁₂

σ₂-act : {A : Set} → YBSolution A → A × A × A → A × A × A
σ₂-act = R₂₃

-- 三重复合
σ₁σ₂σ₁ : {A : Set} → YBSolution A → A × A × A → A × A × A
σ₁σ₂σ₁ S t = σ₁-act S (σ₂-act S (σ₁-act S t))

σ₂σ₁σ₂ : {A : Set} → YBSolution A → A × A × A → A × A × A
σ₂σ₁σ₂ S t = σ₂-act S (σ₁-act S (σ₂-act S t))

-- braid-YB 方程（B₃ braid 关系的 R 嵌入——Faddeev 核心约束）
record YBLaw {A : Set} (S : YBSolution A) : Set where
  field
    yb-braid : ∀ x y z → σ₁σ₂σ₁ S (x , y , z) ≡ σ₂σ₁σ₂ S (x , y , z)

-- ────────────────────────────────────────────────────────────────────
-- §2. braid-rep 诱导引理（YB 解 → B₃ 表示保持 braid 关系）
-- ────────────────────────────────────────────────────────────────────

braid-rep : {A : Set} → (S : YBSolution A) → (L : YBLaw S) → ∀ x y z
          → σ₁σ₂σ₁ S (x , y , z) ≡ σ₂σ₁σ₂ S (x , y , z)
braid-rep S L x y z = YBLaw.yb-braid L x y z

-- 诚实边界：Faddeev-Reshetikhin 真身是量子群/纽结多项式（R-矩阵量子群表示）——
--   本层为 set-theoretic YB 解的 braid 诱导核心（组合骨架）；量子群侧留后续层

-- ────────────────────────────────────────────────────────────────────
-- §5. 量子群骨架（YB 解的代数结构——n≥2 深化）
--   YB 解 R 生成的量子群：R 的 Yang-Baxter 方程 → 量子群的余乘法/余单位
-- ────────────────────────────────────────────────────────────────────

-- 量子群骨架（YB 解的余乘法形——同形可复制）
record QuantumGroupSkeleton : Set₁ where
  field
    R       : YBSolution
    -- 余乘法 Δ：R → R ⊗ R（Yang-Baxter 方程的代数对应）
    -- 余单位 ε：R → k
    -- antipode S：R → R⁻¹
    -- 律：(Δ ⊗ id)∘Δ = (id ⊗ Δ)∘Δ（余结合——YB 方程的对应）
