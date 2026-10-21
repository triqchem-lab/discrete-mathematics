{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.AStepStdStrict
--
-- **`AHomotopy ⊊ AHomotopyStd`（严格包含）** —— 人类 2026-10-21 确认「这个结果有价值」
--
-- ## 为什么值得单独证
--
-- `AStepStd.agda` 只证了 `AH⊆AHStd`（三角口径 ⊆ 标准口径）。
-- **严格性**（存在 `AHomotopyStd` 能粘合而 `AHomotopy` 不能的一对走）才是
-- 「`AStepStd` 确实比 `AStep` 强」的**实质断言** —— 否则 `π₁ᵈˢᵗᵈ` 可能只是 `π₁ᵈ` 的换名。
--
-- ## 见证：2 顶点 2 边图（**比对称 Cayley 图便宜得多**）
--
-- ```
--   G-bt : 顶点 {0,1}，边 0→1 与 1→0（无自环、无弦）
--   cyc2 = (0→1)·(1→0)          （长度 2 的闭走）
-- ```
--
-- | 断言 | 证明 |
-- |---|---|
-- | `AHomotopyStd G-bt cyc2 (nil 0)` | ✅ 一条 `bt`（回溯对 `0→1`、`1→0`）|
-- | `¬ AHomotopy G-bt cyc2 (nil 0)` | ✅ **`G-bt` 无有向三角形 ⇒ `AHomotopy = ≡`**（复用 `no-collapse-iff-triangle-free`）⇒ 若同伦则 `cyc2 ≡ nil`，而 `cons … ≡ nil …` 是构造子冲突 ✗ |
--
-- **⇒ `AHomotopyStd` 严格强于 `AHomotopy`** ✓
--
-- ## 与对称 Cayley 图的对比
--
-- `T6CayleySym` 上同类断言需要「没有 `AStep` 链」的论证（图里有三角形，`NoCollapse` 不可用）；
-- 本模块改用 **无三角形的 2 点图**，让 `NoCollapse` 直接可用 ⇒ 严格性**一次到位** ✓
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `Pi1dCardinality` 的 `no-collapse-iff-triangle-free`（不重证）

module Sovereign.Synthesis.Homotopy.AStepStdStrict where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; AHomotopy)
open import Sovereign.Synthesis.Homotopy.Pi1dCardinality
  using (TriangleFree; NoCollapse; no-collapse-iff-triangle-free)
open import Sovereign.Synthesis.Homotopy.AStepStd
  using (AStepStd; AHomotopyStd; bt; gen)

--------------------------------------------------------------------------------
-- §1. 见证图：2 顶点、2 边（`0→1`、`1→0`），无自环无弦
--------------------------------------------------------------------------------

data E2 : Fin 2 → Fin 2 → Set where
  e01 : E2 Fin.zero (Fin.suc Fin.zero)
  e10 : E2 (Fin.suc Fin.zero) Fin.zero

G-bt : DiGraph
G-bt = record { V = Fin 2 ; edge = E2 }

-- 无有向三角形：两组可复合边，弦分别是 `0→0` 与 `1→1`，都不存在
tf2 : TriangleFree G-bt
tf2 e01 e10 = λ ()
tf2 e10 e01 = λ ()

no-collapse2 : NoCollapse G-bt
no-collapse2 = proj₂ (no-collapse-iff-triangle-free {G = G-bt}) tf2

--------------------------------------------------------------------------------
-- §2. 见证走：长度 2 的闭走 `(0→1)·(1→0)`
--------------------------------------------------------------------------------

cyc2 : Walk G-bt Fin.zero Fin.zero
cyc2 = cons e01 (cons e10 (nil Fin.zero))

-- `cons … ≢ nil …`（构造子冲突）
cyc2≢nil : cyc2 ≢ nil Fin.zero
cyc2≢nil = λ ()

--------------------------------------------------------------------------------
-- §3. ★★ 严格性：标准口径能粘合，三角口径不能
--------------------------------------------------------------------------------

-- `AHomotopyStd` 侧：一条 `bt` 就消掉
yes-AHStd : AHomotopyStd G-bt cyc2 (nil Fin.zero)
yes-AHStd = gen (bt (nil Fin.zero) (nil Fin.zero) e01 e10)

-- `AHomotopy` 侧：不可能（无三角形 ⇒ 退化为命题相等）
no-AH : ¬ (AHomotopy G-bt cyc2 (nil Fin.zero))
no-AH ah = cyc2≢nil (no-collapse2 ah)

-- ★★ 严格包含：存在「标准能、三角不能」的一对走
AHomotopy-strictly-weaker :
    AHomotopyStd G-bt cyc2 (nil Fin.zero)
  × ¬ (AHomotopy G-bt cyc2 (nil Fin.zero))
AHomotopy-strictly-weaker = yes-AHStd , no-AH
