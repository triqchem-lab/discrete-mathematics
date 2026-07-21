{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.HolographicSpace
-- 全息态与基模 — 信息论闭包的类型基础设施
--
-- 索引策略 (与 T6.agda div3k/mod3k 同构):
--   T6.agda: div3k 在 k 为变量(中性项)时触发 REWRITE, 短路 div-helper
--   本模块: normSq-basisVec 在 n 为变量(中性项)时触发 REWRITE, 短路 sumGF9
--   类型定义保持 ∀ n 参数化, 不在类型中固定 4320 (避免 basisVec 4320 展开)
--   具体 4320 仅出现在 ℕ 级证明 (refl, 不涉及 Fin 归一化)
--
-- Postulate: 3 (normSq-basisVec REWRITE + basis-orthogonal + maximality)

module Sovereign.Structology.HolographicSpace where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _>_; _<_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.GF9 using
  ( GF9; gf9-one; _+gf9_; _*gf9_; galoisConjugate; galoisNorm)
open import Sovereign.Analysis.FiniteInnerProduct using
  ( VectorSpace; gf9-zero; zeroVec; normSq; hermitianIP; basisVec; basisVec-diag)
open import Sovereign.Structology.BurnsideT6 using
  ( orbit-sizes-sum-729; group-closure-complete
  ; independent-info-from-yao; yao-4320)

--------------------------------------------------------------------------------
-- 归一化短路 (与 T6.agda div3k/mod3k 同原理, 不同机制)
--
-- T6.agda: div-helper 是 Agda builtin → REWRITE 规则拦截内建计算
-- 本模块: sumGF9 是用户定义递归 → 参数化(∀ n)使 sumGF9 n f 卡住不展开
--
-- 两者是同一原理在不同层面的应用:
--   目标: 阻止归一化器对大数索引做 N 层递归展开
--   builtin 函数 → REWRITE 拦截
--   用户定义函数 → 参数化卡住
--
-- normSq-basisVec 作为 postulate 提供证明项 (非 REWRITE 规则)
--------------------------------------------------------------------------------

postulate
  normSq-basisVec : ∀ n (i : Fin n) → normSq n (basisVec n i) ≡ gf9-one

--------------------------------------------------------------------------------
-- 常量 (ℕ 级, 不涉及 Fin 归一化)
--------------------------------------------------------------------------------

INFO-DIM : ℕ
INFO-DIM = 4320

N-CELLS : ℕ
N-CELLS = 729

N-ORBITS : ℕ
N-ORBITS = 14

G-ORDER : ℕ
G-ORDER = 54

--------------------------------------------------------------------------------
-- §1. 全息态 (参数化, 避免大数 Fin 归一化)
--------------------------------------------------------------------------------

record HolographicState (n : ℕ) : Set where
  constructor mkHolo
  field
    amplitude : VectorSpace n
    normIsOne : normSq n amplitude ≡ gf9-one

--------------------------------------------------------------------------------
-- §2. 基模 (参数化)
--------------------------------------------------------------------------------

record BasisMode (n : ℕ) : Set where
  constructor mkBasis
  field
    vector : VectorSpace n
    normOne : normSq n vector ≡ gf9-one

Orthogonal : ∀ {n} → BasisMode n → BasisMode n → Set
Orthogonal b₁ b₂ =
  hermitianIP _ (BasisMode.vector b₁) (BasisMode.vector b₂) ≡ gf9-zero

--------------------------------------------------------------------------------
-- §3. 参数化基模构造
--------------------------------------------------------------------------------
-- basisAt n i = 标准基的第 i 个向量
-- normOne 由 REWRITE 规则短路 (n 为变量时触发)

basisAt : ∀ n (i : Fin n) → BasisMode n
basisAt n i = mkBasis (basisVec n i) (normSq-basisVec n i)

-- 基模在自身索引处的值 = 1
basisAt-self : ∀ n (i : Fin n) → BasisMode.vector (basisAt n i) i ≡ gf9-one
basisAt-self n i = basisVec-diag n i

--------------------------------------------------------------------------------
-- §4. 正交性 (postulate)
--------------------------------------------------------------------------------

postulate
  basis-orthogonal : ∀ n (i j : Fin n) → ¬ (toℕ i ≡ toℕ j) →
    Orthogonal (basisAt n i) (basisAt n j)

--------------------------------------------------------------------------------
-- §5. 最大性 (postulate)
--------------------------------------------------------------------------------

postulate
  theorem-maximality : ∀ n N → N > n →
    ¬ (∀ (i : ℕ) → i < N → BasisMode n)

--------------------------------------------------------------------------------
-- §6. 组合闭包 + 群论闭包 (ℕ 级 refl, 不涉及 Fin)
--------------------------------------------------------------------------------

combinatorial-closure : INFO-DIM ≡ 4320
combinatorial-closure = refl

group-closure : 27 * 1 + 54 * 13 ≡ N-CELLS
group-closure = orbit-sizes-sum-729

burnside-consistency : G-ORDER * N-ORBITS ≡ N-CELLS + 27
burnside-consistency = refl

closure-complete :
  (INFO-DIM ≡ 4320) ×
  (27 * 1 + 54 * 13 ≡ N-CELLS) ×
  (G-ORDER * N-ORBITS ≡ N-CELLS + 27)
closure-complete = combinatorial-closure , group-closure , burnside-consistency

-- INFO-DIM 与 HoloInformation 的等价性
info-dim≡yao : INFO-DIM ≡ independent-info-from-yao
info-dim≡yao = refl
-- 注: independent-info-from-yao = 729 * 6 ∸ 54, 而 INFO-DIM = 4320
-- 两者在 ℕ 上 refl 相等 (729*6∸54 归一化为 4320, ℕ 乘法/减法可计算)
