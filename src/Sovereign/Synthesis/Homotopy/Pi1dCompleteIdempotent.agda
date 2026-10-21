{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi1dCompleteIdempotent
--
-- **完全图 ⇒ 幂等**（`PIO-1.conj.complete-graph-criterion` 的 ⟸ 方向）
--
-- ## 背景
--
-- 台账 `PIO-1.conj.complete-graph-criterion` 的 **⟹ 方向已被证伪**
-- （`Pi1dIdempotentCounterexample`：2 顶点单边 DAG 的 π₁ᵈ 幂等但图不完全）。
-- **本模块证 ⟸ 方向**：
--
-- ```
--   IsComplete G  ⇒  ∀ {v} (w : Walk G v v) → AHomotopy G (w ++w w) w
-- ```
--
-- ## 层次定位（按 2026-10-21 人类裁决 1）
--
-- ⚠ 这是**截断②（一般图 π₁ᵈ）的结构定理**，属投影层，**不是本源命题**。
-- 它有价值（刻画 `Loop / AHomotopy` 何时幂等），但不服务任何本源目标。
--
-- ## ★ 证明结构：不需要 WF 递归
--
-- 直觉上要「把走反复缩短到长度 1」，而缩短后的走**不是原项的子项** ⇒ 看似需要
-- `walk-len` 上的良基递归。但不需要 —— 只要把归纳变元换成**「首边 + 尾走」分解**：
--
-- ```
-- canon : (a : V) (e : edge v a) (p : Walk a v)
--       → AHomotopy (cons e p) (cons (c v v) (nil v))
-- ```
--   · `p = nil`     ⇒ `loop-eq e (c v v)`
--   · `p = cons e' rest`
--       ⇒ `shorten c e e' rest : AStep (cons e (cons e' rest)) (cons (c v rest) rest)`
--         再递归 `canon rest (c v _)`  —— **`rest` 是 `p` 的真子项** ✓
--
-- ⇒ 归纳变量是 `p`（结构递归成立），**完全不需要 ℕ 尺子** ✓
--   （这一点也顺带符合裁决 1 的精神：不用特征 0 的度量做语义装置）
--
-- 主定理则**两侧各规范一次**：
-- ```
--   w      = cons e rest            ⁓  canon-target   （canon c e rest）
--   w · w  = cons e (rest ++w w)    ⁓  canon-target   （canon c e (rest ++w w)）
-- ```
-- 两条 `AHomotopy` 拼起来即得 ✓
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 结构递归 + 结构性 `AHomotopy`，不用 `walk-len`

module Sovereign.Synthesis.Homotopy.Pi1dCompleteIdempotent where

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AHomotopy;
         refl'; gen; AH-trans; AH-symm)
open DiGraph using (V; edge)
open import Sovereign.Synthesis.Homotopy.Pi1dLoops
  using (IsComplete; loop-eq; shorten)

--------------------------------------------------------------------------------
-- §1. ★ 规范化：任一「首边 + 尾走」都 A-同伦到唯一的规范自环
--------------------------------------------------------------------------------

canon : ∀ {G : DiGraph} (c : IsComplete G) {v : V G}
      → (a : V G) (e : edge G v a) (p : Walk G a v)
      → AHomotopy G (cons e p) (cons (c v v) (nil v))
-- ⚠ 不要把 `a` 写成点模式 `.v`：那会让索引统一变成 `v ≟ v`，
--   without-K 下直接 SplitError（2026-10-21 实测）。让它由 `nil` 的出现自然确定。
canon c a e (nil x) = loop-eq e (c _ _)
canon c a e (cons e' rest) =
  AH-trans (gen (shorten c e e' rest)) (canon c _ (c _ _) rest)

--------------------------------------------------------------------------------
-- §2. ⚠ 主定理的实际边界（不硬凑）
--
-- 想要的陈述：
-- ```
--   complete-idempotent : (c : IsComplete G) (w : Walk G v v) → AHomotopy G (w ++w w) w
-- ```
-- 证明上两侧各规范一次即可（`canon` 已证）：
-- ```
--   w = cons e rest  ⇒  w ⁓ canon-target 且 w·w ⁓ canon-target  ⇒  w·w ⁓ w
--   w = nil v       ⇒  w·w = nil ⇒ refl'
-- ```
-- **但第一步的 case split 在本形态下不可做**：
--   `Walk G v v` 的**同一个变量 `v` 出现在索引两侧**，without-K（库开 `--cubical`）
--   禁止消除自反方程 `v ≟ v` ⇒ `SplitError.UnificationStuck` ✗
--   （实测 2026-10-21，见 prover_limits `agda-without-k-reflexive-index-split`）
--
-- **可行的三条出路**（未择一，需人类定）：
--   1. 把顶点类型具体化（如 `V = Fin n`），先按顶点穷举再 split —— `Pi1dCycleThree` 就是这么做的 ✓
--   2. 给定理加一个**显式的「非空/空」见证参数**（`⊎` 型），把 case split 移到调用点；
--   3. 放弃闭走形态，只对「首边 + 尾走」陈述（即 `canon` 的形态）—— 已证 ✓
--
-- 本模块因此**只交付 `canon`**；主定理登记为台账 `PIO-1.thm.complete-idempotent` 的
-- blocked 理由，不缩陈述、不假装完成。
--------------------------------------------------------------------------------
