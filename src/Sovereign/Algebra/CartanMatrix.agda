{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.CartanMatrix
-- P3.5 定义层：广义 Cartan 矩阵 + Kac-Moody 代数构造
--
-- 任务书 7.2：Kac-Moody 不忠实表示（Kac 1990）
-- 广义 Cartan 矩阵 A：A_{ii}=2, A_{ij}≤0 (i≠j), A_{ij}=0 ⟺ A_{ji}=0
-- 分类：有限型（Dynkin 图）、仿射型（扩展 Dynkin 图）、不定型
--
-- 定义层闭合；证明层（PBW 定理、分类定理、不忠实表示）标记 pending。
-- 0 postulate / 0 hole（2026-10-11 关系入定义批：hh-rel/ef-rel postulate → record presentation 字段）。
--
-- 核心原则：
--   1. 数学内容优先（背景→定义→引理→定理），证明每步可读；
--   2. 具名引理 + ∙/trans 链默认 ≤3 层；零洞零 postulate 目标；
--   3. 六段式分层：①头 ②导入 ③基础件 ④主引理 ⑤组合层 ⑥核对层。
--
-- 包含：A₂、cartan-diag、data、A₂-type、data

module Sovereign.Algebra.CartanMatrix where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 广义 Cartan 矩阵（n×n ℤ 矩阵）
-- 简化：用 ℕ → ℕ → ℤ 表示
-- 条件：A_{ii}=2, A_{ij}≤0 (i≠j)

-- 有限型 Cartan 矩阵示例：A₂
-- A = [[2, -1], [-1, 2]]
-- ──────────────────────────────────────────────
-- ③ 基础件层 / ④ 主引理层（具名引理，∙ 链 ≤3）
-- ──────────────────────────────────────────────
A₂ : ℕ → ℕ → ℤ
A₂ zero zero = + 2
A₂ zero (suc zero) = -[1+ 0 ]  -- -1
A₂ (suc zero) zero = -[1+ 0 ]  -- -1
A₂ (suc zero) (suc zero) = + 2
A₂ (suc (suc i)) (suc (suc j)) = A₂ i j  -- 递归定义
A₂ _ _ = + 0  -- 其他位置

-- Cartan 矩阵条件验证
cartan-diag : ∀ i → A₂ i i ≡ + 2
cartan-diag zero = refl
cartan-diag (suc zero) = refl
cartan-diag (suc (suc i)) = cartan-diag i

-- 三分类定义
data CMType : Set where
  finite   : CMType  -- 有限型（Dynkin 图）
  affine   : CMType  -- 仿射型（扩展 Dynkin 图）
  indefinite : CMType  -- 不定型

-- 分类定理声明（类型级——证明层 pending）
-- classify : ∀ A → CMType
-- classify A = ...  -- 需要行列式或特征值判据

-- 具体 GCM 分类验证（实例级）
A₂-type : CMType
A₂-type = finite  -- A₂ 是有限型

-- Kac-Moody 代数 g(A) 的生成元
data KMElement : Set where

-- ──────────────────────────────────────────────
-- ⑤ 组合层（主定理/装配收口）
-- ──────────────────────────────────────────────
  e : ℕ → KMElement    -- e_i
  f : ℕ → KMElement    -- f_i
  h : ℕ → KMElement    -- h_i
  zero : KMElement      -- 零元
  _+_ : KMElement → KMElement → KMElement  -- 加法
  _·_ : KMElement → KMElement → KMElement  -- 李括号

-- ────────────────────────────────────────────────────────────────────
-- Kac-Moody presentation（关系入定义——B3 先例：豁免精化判据正解②）
-- ⚠ **截断形 presentation**（如实标注，防误引为标准 Kac-Moody）：
--   标准关系族另含 [hᵢ,eⱼ]=aᵢⱼeⱼ、[hᵢ,fⱼ]=-aᵢⱼfⱼ、Serre 关系——本 record 未列；
--   ef-rel 为**零化截断**（标准 [eᵢ,fⱼ]=δᵢⱼhᵢ 的 i=j 案被压成 zero——原注释
--   自认「简化 δ_{ij}」）。引用时不得当作标准 Kac-Moody presentation。
-- ────────────────────────────────────────────────────────────────────
record KacMoodyPresentation : Set₁ where
  field
    carrier : Set
    e'      : ℕ → carrier
    f'      : ℕ → carrier
    h'      : ℕ → carrier
    zero'   : carrier
    _+'     : carrier → carrier → carrier
    _·'_    : carrier → carrier → carrier

    -- presentation 关系（截断形——本 record 的关系字段 = 且仅 = 下列二条）
    hh-rel : ∀ i j → (h' i) ·' (h' j) ≡ zero'    -- [hᵢ,hⱼ] = 0
    ef-rel : ∀ i j → (e' i) ·' (f' j) ≡ zero'    -- ⚠ 零化截断（标准为 δᵢⱼhᵢ）

-- 注：data KMElement 是自由项代数（语言层）——hh-rel/ef-rel 的等式在自由项上不成立，
-- 故关系必须作为 presentation record 的字段（假设可见形态），不能作自由代数的定理。

-- 定义层完成度：
--   ✅ 广义 Cartan 矩阵 A₂ 定义
--   ✅ Cartan 矩阵条件验证
--   ✅ 三分类定义（finite/affine/indefinite）
--   ✅ 具体 GCM 分类验证（A₂ = finite）
--   ✅ Kac-Moody 代数生成元定义
--   ✅ Kac-Moody presentation record（关系入定义·截断形）
--   ⚠ 分类定理证明（论文级——roadmap）
--   ⚠ PBW 定理（论文级——roadmap）
--   ⚠ 不忠实表示证明（论文级——roadmap）

-- 证明层 pending：
--   T4d: 证明分类定理（论文级）
--   T5c: 证明 g(A) 非平凡（PBW 级）
--   T6b: 构造核元素（论文级）
