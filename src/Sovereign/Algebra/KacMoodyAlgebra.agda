{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.KacMoodyAlgebra
-- Kac-Moody 代数定义层：广义 Cartan 矩阵类型 + A₂ 实例 + 生成元
--
-- 数学背景（Kac 1990, Infinite Dimensional Lie Algebras）：
--   广义 Cartan 矩阵（GCM）：A_{ii}=2, A_{ij}≤0 (i≠j), A_{ij}=0 ⟺ A_{ji}=0
--   Kac-Moody 代数 g(A)：由 e_i/f_i/h_i 生成，Chevalley 关系
--   任务书 7.2 对应层；不忠实表示的实质证明见 TrivialRepUnfaithful（平凡表示论证——原 KacMoodyFaithful 重命名，避免与任务书 7.2 K(E10) 特定主张混淆）
--
-- 0 postulate / 0 hole。定理层（Chevalley 关系推导/PBW/分类）roadmap。
module Sovereign.Algebra.KacMoodyAlgebra where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_]; 0ℤ)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- §1. 广义 Cartan 矩阵类型
--------------------------------------------------------------------------------

-- GCM 条件：对角 2，非对角 ≤0，对称零模式
-- 整数记号 helper（先于使用定义——Agda 顺序作用域）
pos : ℕ → ℤ
pos = +_
neg? : ℤ → Set
neg? (-[1+ _ ]) = ⊤
neg? _ = ⊥
isZero : ℤ → ℕ
isZero (+ zero) = 1
isZero _ = 0

record IsGCM (n : ℕ) (A : ℕ → ℕ → ℤ) : Set where
  field
    diag-2   : ∀ i → A i i ≡ pos 2
    off-neg  : ∀ i j → ¬ (i ≡ j) → neg? (A i j)
    sym-zero : ∀ i j → isZero (A i j) ≡ isZero (A j i)

--------------------------------------------------------------------------------
-- §2. A₂ 实例：[[2,-1],[-1,2]]
--------------------------------------------------------------------------------

A₂ : ℕ → ℕ → ℤ
A₂ zero zero = pos 2
A₂ zero (suc zero) = -[1+ zero ]
A₂ (suc zero) zero = -[1+ zero ]
A₂ (suc zero) (suc zero) = pos 2
A₂ _ _ = 0ℤ

-- A₂ 的对角条件（限定 2×2 块——i≥2 时 A₂ i i = 0ℤ 不满足 GCM，属块外延伸）
A₂-diag0 : A₂ 0 0 ≡ pos 2
A₂-diag0 = refl
A₂-diag1 : A₂ 1 1 ≡ pos 2
A₂-diag1 = refl

-- A₂ 对称性：A₂ i j ≡ A₂ j i（GCM 的对称零模式在此例中升级为完全对称）
A₂-sym : ∀ i j → A₂ i j ≡ A₂ j i
A₂-sym zero zero = refl
A₂-sym zero (suc zero) = refl
A₂-sym zero (suc (suc _)) = refl          -- 两侧均落 catchall 0ℤ
A₂-sym (suc zero) zero = refl
A₂-sym (suc zero) (suc zero) = refl
A₂-sym (suc zero) (suc (suc _)) = refl
A₂-sym (suc (suc _)) zero = refl
A₂-sym (suc (suc _)) (suc zero) = refl
A₂-sym (suc (suc _)) (suc (suc _)) = refl

--------------------------------------------------------------------------------
-- §3. Kac-Moody 生成元类型（自由代数层——关系定理 roadmap）
--------------------------------------------------------------------------------

data KMGen : Set where
  km-e : ℕ → KMGen    -- e_i（正根生成元）
  km-f : ℕ → KMGen    -- f_i（负根生成元）
  km-h : ℕ → KMGen    -- h_i（Cartan 子代数）

-- Chevalley 关系（陈述层——推导需李代数基础设施，roadmap）：
--   [h_i, h_j] = 0；[e_i, f_j] = δᵢⱼ h_i；[h_i, e_j] = A_{ij} e_j
-- 实质不忠实表示证明（平凡表示论证）已在 TrivialRepUnfaithful 闭合。

-- ────────────────────────────────────────────────────────────────────
-- §5. Kac-Moody n≥2 深化（高阶根系骨架）
--   n=2 的 Kac-Moody 代数：Cartan 矩阵 A = [[2,-a],[-b,2]] → 根系 Φ
-- ────────────────────────────────────────────────────────────────────

-- n=2 Kac-Moody 骨架（Cartan 矩阵 → 根系）
record KacMoody2 : Set where
  field
    a b     : ℕ                    -- Cartan 矩阵参数 [[2,-a],[-b,2]]
    -- Weyl 群：s₁, s₂ 的反射（根系的对称）
    s₁ s₂   : ℕ → ℕ → ℕ → ℕ
    -- Serre 关系：[eᵢ, fᵢ] = hᵢ（生成元的代数关系）
    Serre   : ℕ → ℕ → ℕ → ℕ
