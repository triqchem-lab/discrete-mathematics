{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi1dLoops
--
-- **自环的 A-同伦律 + 「完全图 ⇒ 幂等」的缩短机制**
--
-- ## 背景
--
-- 台账 `PIO-1.conj.complete-graph-criterion` 的**⟹ 方向已被证伪**
-- （`Pi1dIdempotentCounterexample`：2 顶点单边 DAG 的 π₁ᵈ 幂等但图不完全）。
-- **⟸ 方向（完全 ⇒ 幂等）仍未证**，本模块给出它实际需要的两块机制。
--
-- ## 本模块证了什么
--
-- ### ① 同一顶点的任意两条自环 A-同伦（**不需要完全性**）★
--
-- ```
-- loop-eq : (e e' : edge v v) → AHomotopy G (cons e (nil v)) (cons e' (nil v))
-- ```
--
-- 机制：`expand` 把一条自环**展开**成「两条」，`slide` 再收回到另一条 ✓
-- ```
--   cons e (nil v)  ──expand(e,e,e)──▶  cons e (cons e (nil v))
--                                          │
--                                          └──slide(e,e,e')──▶  cons e' (nil v)
-- ```
-- **⇒ 「自环」在 π₁ᵈ 里只有一个元素**（只要 `edge v v` 非空）✓
--
-- ### ② 单边闭走幂等（**不需要完全性**）★
--
-- ```
-- loop-idempotent : (∀ e : edge v v) → AHomotopy G (w ++w w) w   where w = cons e (nil v)
-- ```
-- 机制就是 `slide (nil v) (nil v) e e e` —— 三角形三条边都取同一条自环 ✓
--
-- ### ③ 完全图里的**缩短步**（⟸ 方向的主装置）
--
-- ```
-- shorten : IsComplete G → AStep G (cons e1 (cons e2 b)) (cons (c x z) b)
-- ```
-- 任意两条相邻边可经 `slide` 换成一条（第三条边由完全性提供）✓
-- ⇒ 任何长度 ≥ 2 的走都能**逐步缩短 1**，这是「完全 ⇒ 幂等」归纳证明的核心步。
--
-- ## ⚠ 本模块**不**证什么
--
--   · **不**证「完全 ⇒ 幂等」的完整陈述 ✗ —— 还需对走归纳：把 `w` 与 `w·w` 都缩短到
--     长度 1，再用 ① 的 `loop-eq` 得同一条自环。已立节点 `PIO-1.count` 之外的后续任务，
--     不在此处冒充完成。
--   · **不**断言⟹方向 —— 已 refuted，勿重走 ✗
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 只用 `AStep` 的两个构造子，不需要任何额外假设 ✓

module Sovereign.Synthesis.Homotopy.Pi1dLoops where

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AStep; slide; expand;
         AHomotopy; gen; AH-trans)
open DiGraph using (V; edge)

--------------------------------------------------------------------------------
-- §1. 完全性谓词
--------------------------------------------------------------------------------

IsComplete : DiGraph → Set
IsComplete G = ∀ (u v : V G) → edge G u v

--------------------------------------------------------------------------------
-- §2. ★ 同一顶点的任意两条自环 A-同伦（不需要完全性）
--------------------------------------------------------------------------------

loop-eq : ∀ {G : DiGraph} {v : V G} (e e' : edge G v v)
        → AHomotopy G (cons e (nil v)) (cons e' (nil v))
loop-eq {G} {v} e e' =
  AH-trans
    (gen (expand (nil v) (nil v) e e e))
    (gen (slide  (nil v) (nil v) e e e'))

--------------------------------------------------------------------------------
-- §3. ★ 单边闭走幂等（不需要完全性）
--------------------------------------------------------------------------------

loop-idempotent : ∀ {G : DiGraph} {v : V G} (e : edge G v v)
                → AHomotopy G (cons e (nil v) ++w cons e (nil v)) (cons e (nil v))
loop-idempotent {G} {v} e = gen (slide (nil v) (nil v) e e e)

--------------------------------------------------------------------------------
-- §4. 完全图里的缩短步（⟸ 方向的主装置）
--------------------------------------------------------------------------------

-- 两条相邻边 `x→y→z` 缩短成一条 `x→z`（第三条边由完全性提供）
shorten : ∀ {G : DiGraph} (c : IsComplete G) {x y z v : V G}
          (e1 : edge G x y) (e2 : edge G y z) (b : Walk G z v)
        → AStep G (cons e1 (cons e2 b)) (cons (c x z) b)
shorten c {x} e1 e2 b = slide (nil x) b e1 e2 (c _ _)
