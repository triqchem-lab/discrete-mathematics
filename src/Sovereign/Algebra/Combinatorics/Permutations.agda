{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Combinatorics.Permutations
-- 置换群基础：Sym n（有限双射）的幺半群律、对换/三周期、符号同态实例
--
-- 数学背景：Sym n = Fin n 的双射集合（stdlib `Data.Fin.Permutation` **直用**——
--   Permutation m n = Fin m ↔ Fin n；to/from = ⟨$⟩ʳ/⟨$⟩ˡ；组合理论 = _∘ₚ_）。
--   群律（结合/单位/逆）以点态等价 _≈_ 承载（免 funext）；对换 transpose i j
--   为生成元面（循环分解立界 §5）。
--
-- 核心原则：
-- 1. stdlib 为信任基座直 import（permutation/inverseˡ/ʳ/transpose 零重证）
-- 2. 群律全构造性（点态 refl / 逆引理直调）
-- 3. sgn 以 n=2 全表实例核对承载（一般同态定理立界——不设空壳签名）
-- 4. 复用注记：A₄/S₃ 表示面（Structology.S3IsGL22 mul-hom :107-109 /
--    A4Group / SL23Cayley / FiniteGroupAxioms）——Fin 3 置换即 S₃ 载体
-- 5. 穷举边界：实例核对 ≤27 case（本件最大 3 点 × refl）
--
-- 包含：幺半群律 ×3 · 逆元律 ×2 · transpose 实例 · c3 三周期 · sgn₂ 同态表
--       · 核对层 · 立界注记

module Sovereign.Algebra.Combinatorics.Permutations where

open import Data.Fin using (Fin; toℕ)
  renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; not)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Data.Fin.Permutation
  using (Permutation; Permutation′; _⟨$⟩ʳ_; _⟨$⟩ˡ_; inverseˡ; inverseʳ;
         id; flip; _∘ₚ_; _≈_; transpose)

------------------------------------------------------------------------
-- §1 主引理层：Sym n 幺半群律（点态等价承载——免 funext）
------------------------------------------------------------------------

-- 结合律：(π∘ρ)∘σ ≈ π∘(ρ∘σ)——函数应用嵌套的定义相等
∘ₚ-assoc : ∀ {n} (π ρ σ : Permutation′ n) → (π ∘ₚ ρ) ∘ₚ σ ≈ π ∘ₚ (ρ ∘ₚ σ)
∘ₚ-assoc π ρ σ i = refl

-- 左单位：id ∘ₚ π ≈ π
∘ₚ-idˡ : ∀ {n} (π : Permutation′ n) → id ∘ₚ π ≈ π
∘ₚ-idˡ π i = refl

-- 右单位：π ∘ₚ id ≈ π
∘ₚ-idʳ : ∀ {n} (π : Permutation′ n) → π ∘ₚ id ≈ π
∘ₚ-idʳ π i = refl

------------------------------------------------------------------------
-- §2 逆元律：flip π = 逆置换（stdlib inverseˡ/ʳ 直调）
------------------------------------------------------------------------

-- 左逆：flip π ∘ₚ π ≈ id（to = π⟨$⟩ʳ ∘ π⟨$⟩ˡ = inverseʳ）
∘ₚ-invˡ : ∀ {n} (π : Permutation′ n) → flip π ∘ₚ π ≈ id
∘ₚ-invˡ π i = inverseʳ π

-- 右逆：π ∘ₚ flip π ≈ id（to = π⟨$⟩ˡ ∘ π⟨$⟩ʳ = inverseˡ）
∘ₚ-invʳ : ∀ {n} (π : Permutation′ n) → π ∘ₚ flip π ≈ id
∘ₚ-invʳ π i = inverseˡ π

------------------------------------------------------------------------
-- §3 实例层：对换与三周期（Fin 2/Fin 3 具体形）
------------------------------------------------------------------------

-- Fin 2 对换（唯一非平凡元）
t01 : Permutation′ 2
t01 = transpose fzero (fsuc fzero)

-- 对合律（Fin 2 具体——2 点 refl；一般形立界 §5）
transpose-invol2 : t01 ∘ₚ t01 ≈ id
transpose-invol2 fzero       = refl
transpose-invol2 (fsuc fzero) = refl

-- Fin 3 三周期：c3 = 两个相邻对换的复合（S₃ 的 3-周期载体）
c3 : Permutation′ 3
c3 = transpose fzero (fsuc fzero) ∘ₚ transpose (fsuc fzero) (fsuc (fsuc fzero))

-- 三周期性：c3³ ≈ id（3 点逐点归约——≤27 case 穷举边界内）
c3-order3 : c3 ∘ₚ (c3 ∘ₚ c3) ≈ id
c3-order3 fzero                = refl
c3-order3 (fsuc fzero)         = refl
c3-order3 (fsuc (fsuc fzero))  = refl

------------------------------------------------------------------------
-- §4 实例层：符号同态（n=2 全表——偶=恒等型）
------------------------------------------------------------------------

-- sgn₂：true = 偶（π(f₀)=f₀）／false = 奇（π(f₀)=f₁）
sgn₂ : Permutation′ 2 → Bool
sgn₂ π = not (fsuc-in-π π)
  where
  -- π(f₀) 是否为 f₁（构造子判定——免 == 比较器）
  fsuc-in-π : Permutation′ 2 → Bool
  fsuc-in-π π with π ⟨$⟩ʳ fzero
  ... | fzero      = false
  ... | fsuc fzero = true

-- 表值核对
check-sgn-id : sgn₂ id ≡ true
check-sgn-id = refl

check-sgn-t : sgn₂ t01 ≡ false
check-sgn-t = refl

-- 同态表 ×4（n=2 全域穷举——符号乘法 = 同偶性）：
-- 偶∘偶=偶 / 偶∘奇=奇 / 奇∘偶=奇 / 奇∘奇=偶
check-sgn-hom-pp : sgn₂ (id ∘ₚ id) ≡ true
check-sgn-hom-pp = refl

check-sgn-hom-pt : sgn₂ (id ∘ₚ t01) ≡ false
check-sgn-hom-pt = refl

check-sgn-hom-tp : sgn₂ (t01 ∘ₚ id) ≡ false
check-sgn-hom-tp = refl

check-sgn-hom-tt : sgn₂ (t01 ∘ₚ t01) ≡ true
check-sgn-hom-tt = refl

------------------------------------------------------------------------
-- §5 核对层 + 立界注记（诚实边界——不设空壳签名）
------------------------------------------------------------------------

-- 逆元律实例核对（Fin 2：flip t01 ∘ₚ t01 = id 逐点）
check-inv-t01 : flip t01 ∘ₚ t01 ≈ id
check-inv-t01 = ∘ₚ-invˡ t01

-- 立界（如实）：
-- (i) 一般对合律 transpose i j ∘ₚ transpose i j ≈ id（需 PC.transpose 的
--     对称形引理——stdlib Components 面 ~20-40 行）；
-- (ii) 循环分解一般形（任意置换 = 不交轮换之积——经典定理 ~200-300 行，
--     依赖对换生成性立界）；
-- (iii) sgn 同态一般形（sgn : Sym n → {±1} 乘法同态——逆序数/轮换奇偶
--     二路线均 ~150-250 行；本件 n=2 全表为实例核对非一般定理）；
-- (iv) Sym n 群律 record 化（UniversalAlgebra.Group 承载——接
--     FiniteGroupAxioms 面）；
-- 对账注记：Fin 3 六置换 = S₃ 载体（S3IsGL22.mul-hom :107-109 /
-- A4Group 面衔接——本件 c3 即 S₃ 的 3-周期，c3-order3 即其阶律核对）。
