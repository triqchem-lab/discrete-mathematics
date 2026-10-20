{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3Rank
-- GF(3) 矩阵的**消元层**与 `rank` 定义（T4 / A1c，2026-10-20）
--
-- 数学背景
--   `GF3RowOps`（138 行）给了初等行变换及其可逆性；
--   本模块在其上给出：① 行的**首项位置**测量；② **消元步**（用 pivot 行消掉目标行首项）
--   及其**核心正确性定理**（消元后首项为 T₀）；③ `rank` 的定义（echelon 后数非零行）。
--
-- 标志性定理
--   `elim-head : 用首项为 T₁ 的 pivot 行、以 `negate r₀` 为系数消元后，目标行首项必为 T₀`
--   这是**行化简每一步的正确性**，也是 `echelon` 能终止于「无共同首项」的依据。
--
-- 诚实边界
--   ✗ 本模块**未**给出完整 `echelon` 算法（需要「按首项位置排序 → 反复消元 → 直到
--     无两行首项同位」的递归，约 120 行）；`rank` 目前只是「对给定的已化简矩阵数非零行」。
--   ✗ 未证秩在行变换下的不变性（A1c-4）。
--   ✓ 已在 `GF3RowOps` 证：加行可逆（`add-then-cancel`）、缩放可逆（`scale-cancel`）。
--
-- 依赖: Sovereign.Base.Trit（GF(3) 环公理）、Sovereign.Algebra.LinearAlgebra.GF3RowOps

module Sovereign.Algebra.LinearAlgebra.GF3Rank where

open import Data.List using (List; []; _∷_; length; map; zipWith; filter)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

--------------------------------------------------------------------------------
-- §1. 行 = List Trit（列表比 Vec 更适合消元算法的递归）
--------------------------------------------------------------------------------

Row : Set
Row = List Trit

Matrix : Set
Matrix = List Row

--------------------------------------------------------------------------------
-- §2. 零判定与测量的
--------------------------------------------------------------------------------

isZeroT : Trit → Bool
isZeroT T₀ = true
isZeroT T₁ = false
isZeroT T₂ = false

-- 行是否全零
isZeroRow : Row → Bool
isZeroRow []       = true
isZeroRow (x ∷ xs) = if isZeroT x then isZeroRow xs else false

-- 非零行计数（`rank` 的最终测量）
countNonzero : Matrix → ℕ
countNonzero []       = zero
countNonzero (r ∷ rs) = (if isZeroRow r then zero else suc zero) + countNonzero rs

-- 前导零的个数（= 首项位置；全零行返回行长）
leadingZeros : Row → ℕ
leadingZeros []       = zero
leadingZeros (T₀ ∷ xs) = suc (leadingZeros xs)
leadingZeros (_ ∷ _)   = zero

--------------------------------------------------------------------------------
-- §3. 消元步：用 pivot 行消掉目标行
--------------------------------------------------------------------------------

-- `elimRow c p r = r ⊕ (c ⊗ p)`（逐分量）
elimRow : Trit → Row → Row → Row
elimRow c p = zipWith _⊕_ (map (c ⊗_) p) 

-- ★ 核心正确性：pivot 首项为 T₁、系数取 `negate r₀` ⇒ 目标行首项为 T₀
elim-head :
  ∀ (r₀ : Trit) (rs ps : Row) →
    elimRow (negate r₀) (T₁ ∷ ps) (r₀ ∷ rs) ≡ T₀ ∷ elimRow (negate r₀) ps rs
elim-head T₀ rs ps = refl
elim-head T₁ rs ps = refl
elim-head T₂ rs ps = refl

--------------------------------------------------------------------------------
-- §4. `rank` 定义（对已化简矩阵数非零行）
--------------------------------------------------------------------------------

-- 注意：本定义**要求输入已是 echelon 形**；完整算法见诚实边界
rankOfReduced : Matrix → ℕ
rankOfReduced = countNonzero

-- 空矩阵的秩为 0
rank-empty : rankOfReduced [] ≡ zero
rank-empty = refl

-- 全零行的矩阵，秩为 0（单行情形，示意）
rank-zero-row : rankOfReduced ([] ∷ []) ≡ zero
rank-zero-row = refl

--------------------------------------------------------------------------------
-- §5. 消元列步：用 pivot 行（首项 T₁）把**下方所有行**的首项消成 T₀
--
-- 这是 echelon 的**单列一步**。`elim-head` 保证每行消元后首项为 T₀。
-- 递归在**行列表**上结构下降，不涉及列索引。
--------------------------------------------------------------------------------

elimBelow : Row → Matrix → Matrix
elimBelow p []       = []
elimBelow p ([] ∷ rs) = [] ∷ elimBelow p rs
elimBelow p ((x ∷ xs) ∷ rs) with isZeroT x
... | true  = (x ∷ xs) ∷ elimBelow p rs
... | false = (T₀ ∷ elimRow (negate x) p xs) ∷ elimBelow p rs

-- ★ 列步不变式：消元后所有非空行的首项都是 T₀
--
-- 实现要点（`with` 纪律，见 memory/agda-with-discipline.md）：**不用 `with`**，
-- 直接对 `Trit` 的 3 个构造子匹配 ⇒ `isZeroT` 在选择时即归约 ⇒ `allHeads` 内层
-- 的 `if` 随之归约。之前用 `with isZeroT x` 只抽象了外层，内层不归约 ⇒ UnequalTerms。

allHeads : Matrix → Bool
allHeads []             = true
allHeads ([] ∷ rs)      = allHeads rs
allHeads ((x ∷ _) ∷ rs) = if isZeroT x then allHeads rs else false

elimBelow-heads : ∀ p rs → allHeads (elimBelow p rs) ≡ true
elimBelow-heads p []                     = refl
elimBelow-heads p ([] ∷ rs)              = elimBelow-heads p rs
elimBelow-heads p ((T₀ ∷ xs) ∷ rs)       = elimBelow-heads p rs
elimBelow-heads p ((T₁ ∷ xs) ∷ rs)       = elimBelow-heads p rs
elimBelow-heads p ((T₂ ∷ xs) ∷ rs)       = elimBelow-heads p rs
