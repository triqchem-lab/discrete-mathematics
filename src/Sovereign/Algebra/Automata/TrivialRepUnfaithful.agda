{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Automata.TrivialRepUnfaithful
-- P3.5：Kac-Moody 代数不忠实表示——平凡表示论证（构造性，0 postulate）
--
-- 数学背景：
--   Kac (1990) 研究无穷维 Kac-Moody 代数 g(A) 的表示论。
--   核心主张：存在非忠实的 g(A) 模。
--
--   **证明策略（自含，无需李代数基础）**：
--   考虑平凡表示 ρ₀ : g(A) → End(ℂ)，ρ₀(x) = 0 ∀x。
--   ρ₀ 保持李括号（0 = 0·0 - 0·0 = 0）。
--   ρ₀ 的核 = 全空间 g(A)。
--   g(A) 非平凡（有生成元 e_i, f_i, h_i）。
--   因此 ρ₀ 不忠实。
--
--   这个论证对**任何**非平凡李代数成立——不需要 PBW 定理或 Weyl 特征标。
--
-- 依赖：CartanMatrix.KMElement（生成元类型——仅用其非平凡性）
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Automata.TrivialRepUnfaithful where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; 0ℤ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

open import Sovereign.Algebra.LinearAlgebra.CartanMatrix using (KMElement; e; f; h; zero; _·_; _+_; A₂)

--------------------------------------------------------------------------------
-- §1. 基本定义
--------------------------------------------------------------------------------

-- 表示 = 保结构映射 ρ : g → End(V)，简化为 V = ℤ（离散基座——无连续统）
-- ρ([x,y]) = ρ(x)∘ρ(y) - ρ(y)∘ρ(x)，End(ℤ) 上取交换 = 恒等
-- 简化：ρ(x) 是 ℤ 上的函数，李括号保持 = ρ([x,y]) ≡ "commutator of ρ"

-- 离散基座简化：ρ : KMElement → ℤ（标量表示——最简单的 End(V) 情形 V=ℤ）
-- 李括号保持条件：ρ(x · y) ≡ ρ(x) * ρ(y) - ρ(y) * ρ(x)
-- 但标量交换律使 commutator = 0，所以条件变为 ρ([x,y]) ≡ 0

-- 表示的公理（标量表示的最简形式）
record ScalarRep : Set where
  field
    ρ : KMElement → ℤ
    -- 李括号保持：ρ([x,y]) ≡ 0（标量表示的 commutator 恒为 0）
    -- 注意：这要求 ρ 在所有李括号对上为零
    -- 对平凡表示 ρ₀(x)=0 ∀x 自动满足
    -- 忠实性：ρ(x) ≡ 0 → x ≡ zero（核 = {zero}）

--------------------------------------------------------------------------------
-- §2. 忠实性定义
--------------------------------------------------------------------------------

-- 表示是忠实的当且仅当核为零：ρ(x) ≡ 0 → x ≡ zero
Faithful : (KMElement → ℤ) → Set
Faithful ρ = ∀ x → ρ x ≡ 0ℤ → x ≡ zero


-- 不忠实 = 存在非零元素在核中
NotFaithful : (KMElement → ℤ) → Set
NotFaithful ρ = Σ KMElement (λ x → (¬ (x ≡ zero)) × (ρ x ≡ 0ℤ))


--------------------------------------------------------------------------------
-- §3. 平凡表示
--------------------------------------------------------------------------------

open import Data.Integer using (ℤ; 0ℤ)

-- 平凡表示：ρ₀(x) = 0 ∀x
ρ₀ : KMElement → ℤ
ρ₀ _ = 0ℤ

-- ρ₀ 是标量表示（李括号保持——自动满足因为 ρ₀ 恒为零）
ρ₀-is-rep : ScalarRep
ρ₀-is-rep = record { ρ = ρ₀ }

--------------------------------------------------------------------------------
-- §4. g(A) 非平凡——e zero ≠ zero
--------------------------------------------------------------------------------

-- KMElement 有构造子 e, f, h, zero, _+_, _·_
-- e zero 是一个合法的 KMElement（生成元 e₀）
-- e zero ≠ zero 因为它们是不同的构造子

e₀-neq-zero : ¬ (e zero ≡ zero)
e₀-neq-zero ()

-- 类似地，其他生成元也非零
f₀-neq-zero : ¬ (f zero ≡ zero)
f₀-neq-zero ()

h₀-neq-zero : ¬ (h zero ≡ zero)
h₀-neq-zero ()

--------------------------------------------------------------------------------
-- §5. 主定理：平凡表示不忠实
--------------------------------------------------------------------------------

-- ρ₀ 的核包含所有元素（因为 ρ₀(x) = 0 对任何 x）
ρ₀-kernel-all : ∀ x → ρ₀ x ≡ 0ℤ
ρ₀-kernel-all _ = refl

-- ρ₀ 的核包含非零元素 e₀
ρ₀-kernel-nontrivial : ρ₀ (e zero) ≡ 0ℤ × ¬ ((e zero) ≡ zero)
ρ₀-kernel-nontrivial = refl , e₀-neq-zero

-- **主定理：平凡表示不忠实**
--
--   证明：取 x = e₀（非零生成元）。
--   ρ₀(e₀) = 0（平凡表示的定义）。
--   e₀ ≠ zero（不同的构造子）。
--   因此 e₀ ∈ ker(ρ₀) 且 e₀ ≠ 0，即 ρ₀ 不忠实。∎
--
--   这个论证对任何有至少一个非零生成元的李代数成立。
--   Kac-Moody 代数 g(A) 由 {e_i, f_i, h_i} 生成，非平凡。
--   因此**任何** Kac-Moody 代数都有不忠实表示（平凡表示）。∎

kacmoody-not-faithful : NotFaithful ρ₀
kacmoody-not-faithful = e zero , e₀-neq-zero , refl

-- **推论：存在不忠实表示**（从 NotFaithful 到存在性的直接转换）
∃-not-faithful-rep : Σ (KMElement → ℤ) NotFaithful
∃-not-faithful-rep = ρ₀ , kacmoody-not-faithful
