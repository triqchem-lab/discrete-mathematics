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
-- §2. ★ 出路的实际施工：把 case split 移到**调用点**
--
-- without-K 只禁止「对 `Walk G v v` 做构造子 split」。若把走**已分解**地传进来
-- （`cons e rest`），split 就不需要了 —— 主定理的**实质情形**因此可以证 ✓
--------------------------------------------------------------------------------

complete-idempotent-cons :
    ∀ {G : DiGraph} (c : IsComplete G) {v a : V G}
      (e : edge G v a) (rest : Walk G a v)
    → AHomotopy G (cons e rest ++w cons e rest) (cons e rest)
complete-idempotent-cons c {v} e rest =
  AH-trans (canon c _ e (rest ++w cons e rest))
           (AH-symm (canon c _ e rest))

-- 空走情形（平凡，且**不需要** split：直接对 `nil v` 陈述）
complete-idempotent-nil : ∀ {G : DiGraph} {v : V G}
                        → AHomotopy G (nil v ++w nil v) (nil v)
complete-idempotent-nil = refl' _

--------------------------------------------------------------------------------
-- §3. ⚠ 主定理的实际边界（不硬凑）
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
--   1. 把顶点类型具体化（如 `V = Fin n`），先按顶点穷举再 split
--      —— ⚠ 实测**只对零元构造子有效**（见 §4 ③）；`Pi1dCycleThree` 并未用过此法
--      （它只是**显式构造** `cyc3w`，从未对任意闭走做 split）
--   2. 给定理加一个**显式的「非空/空」见证参数**（`⊎` 型），把 case split 移到调用点；
--   3. 放弃闭走形态，只对「首边 + 尾走」陈述（即 `canon` 的形态）—— 已证 ✓
--
-- 本模块因此**只交付 `canon`**；主定理登记为台账 `PIO-1.thm.complete-idempotent` 的
-- blocked 理由，不缩陈述、不假装完成。

--------------------------------------------------------------------------------
-- §4. 两条**实测失败**的绕法（机器证据；避免后来者重走）
--
-- ① 直接两子句 `complete-idempotent c (nil x) = …` / `(cons e rest) = …` ✗
-- ② Σ 打包（让顶点成为模式变量）：`(p : Σ (V G) (λ v → Walk G v v))` 上分情形 ✗
--
-- 两条报**同一个**错（2026-10-21 实测，探针已删）：
-- ```
-- SplitError.UnificationStuck: I'm not sure if there should be a case for
-- the constructor nil, because I get stuck when trying to solve
--   x ≟ v ／ x ≟ v
-- Possible reason: Cannot eliminate reflexive equation v = v of type V G
--   because K has been disabled.
-- ```
-- ⇒ Σ 打包**不能**把 `v` 变成可统一的口径（`Walk G v v` 的自反索引仍在类型里）。
--
-- ③ 顶点具体化（`V = Fin n`）+ 先按顶点穷举：**部分有效** ⚠
--    在 `FinGraph n E`（顶点**定义性**是 `Fin n`）上实测：
--      · `v = zero`   ⇒ split 通过 ✓（`x ≟ zero` 直接统一）
--      · `v = suc i`  ⇒ **仍失败** ✗，报
--        `x ≟ suc i`（两次）／「Cannot eliminate reflexive equation `i = i`
--        of type `Fin n`」—— `suc` 的单射性把问题拉回 `i = i`。
--    ⇒ 「穷举顶点」只在顶点被**零元构造子**头住时奏效；`Fin n`（n ≥ 2）不满足。
--
-- ④ 端点一般化 + 显式等式（**最接近成功**的一条）：把主定理改成
--    `(w : Walk G u v) (eq : u ≡ v) → AHomotopy G (w ++w subst (λ z → Walk G z v) (sym eq) w) w`
--    ⇒ split 发生在 `Walk G u v`（两端是**不同变量**）上，`cons` 情形可直接用 `canon` ✓；
--    **但 `nil` 情形挂**：此时 `u`、`v` 都实例化为 `x`，`eq : x ≡ x` 是**变量**，
--    `subst P eq (nil x)` **不归约**，而对 `eq : x ≡ x` 做 `J` 正是同一个自反索引墙 ✗
--    （实测报 `eq` 类型期望 `v ≡ _` 与 `u ≡ v` 不符）。
--
-- 同族墙在库内另有一处记录：`Pi1dCardinality.agda:200` 的
-- 「`walk-len w ≡ zero → w ≡ nil u` 在**闭走**形态下**不可证**」——同一个自反索引问题。
--
-- ## 对「三条出路」的修正（每一条都**实测过**，见 §4 ①②③）
--
-- · 第 2 条（显式「非空/空」见证 `⊎`/`Decomp`）**不能**给出一般定理 ——
--   `Decomp w` 对任意 `w : Walk G v v` **本身不可构造**（同一个 split 墙），只是把问题移到调用点；
-- · 第 1 条（顶点类型具体化 + 穷举）**只部分有效** —— 仅当顶点被**零元构造子**头住
--   （如 `Fin` 的 `zero`）时 split 通过；`suc i` 情形仍撞 `i = i`（§4 ③ 实测）；
-- · 第 3 条（`canon` 形态）已证 ✓。
--
-- ⇒ 主定理（抽象 `V` 上的**闭走**形态）在本形式化下**没有已知出路**。
--   可证边界就是：`canon`（首边+尾走）/ `complete-idempotent-cons` / `complete-idempotent-nil`。
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
