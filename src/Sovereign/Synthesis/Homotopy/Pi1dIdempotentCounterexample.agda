{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi1dIdempotentCounterexample
--
-- **反例：`π₁ᵈ(G)` 幂等 ⇏ `G` 完全有向图**
--
-- ## 被检验的猜想
--
-- 台账节点 `PIO-1.conj.complete-graph-criterion`（候选 (a)）：
--
-- > `π₁ᵈ(G)` 幂等 ⟺ `G` 是完全有向图（每对顶点双向有边 + 每点自环）
--
-- 「幂等」= `∀ {v} (w : Walk G v v) → AHomotopy G (w ++w w) w`
--
-- ## 反例（本模块）
--
-- ```
--   G-dag : V = Fin 2，唯一一条边 0 → 1，无其它边
--   0 ──→ 1
-- ```
--
-- **`G-dag` 不是完全有向图** ✓（`edge 0 0 = ⊥`）
-- **但 `π₁ᵈ(G-dag)` 幂等** ✓ —— 因为**唯一的闭走是空走**：
--   · `Walk G-dag 0 0`：`cons` 需要 `edge 0 v`，`edge 0 0 = ⊥`；
--     若 `v = 1` 则剩下 `Walk G-dag 1 0` —— 而 `Walk G-dag 1 0` 空（无入 0 的边）✓
--   · `Walk G-dag 1 1`：`cons` 需要 `edge 1 v`，而 `edge 1 0 = ⊥`、`edge 1 1 = ⊥` ✓
--   ⇒ 闭走只有 `nil`，`nil ++w nil = nil`，故幂等平凡成立 ✓
--
-- ## 结论
--
-- 猜想的 **⟹ 方向为假** ✗ ⇒ 整个双向陈述 **refuted** ✓
-- （⟸ 方向「完全 ⇒ 幂等」本模块不涉及，仍然开放）
--
-- ## 核心原则
--   · 反例必须是**类型级**的（不是「我认为」）✓
--   · 0 postulate / 0 hole
--   · `walk-len w ≡ 0 → w ≡ nil` 在此**不需要** —— 顶点只两个，直接按 `v` 与走形状穷举 ✓
--     （一般形态受 without-K 阻断，见 `Pi1dCardinality` §6 与 prover_limits）

module Sovereign.Synthesis.Homotopy.Pi1dIdempotentCounterexample where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AHomotopy)
open DiGraph using (edge)
open import Sovereign.Synthesis.Homotopy.Pi1dMonoid using (++w-identityʳ)
open import Sovereign.Synthesis.Homotopy.Pi1dCardinality using (≡→AH)

--------------------------------------------------------------------------------
-- §1. 反例图：2 顶点，唯一一条边 0 → 1
--------------------------------------------------------------------------------

edgeD : Fin 2 → Fin 2 → Set
edgeD Fin.zero           Fin.zero           = ⊥
edgeD Fin.zero           (Fin.suc Fin.zero) = ⊤
edgeD (Fin.suc Fin.zero) Fin.zero           = ⊥
edgeD (Fin.suc Fin.zero) (Fin.suc Fin.zero) = ⊥

G-dag : DiGraph
G-dag = record { V = Fin 2 ; edge = edgeD }

--------------------------------------------------------------------------------
-- §2. 没有从 1 出发的边，也没有「到 0」的走
--------------------------------------------------------------------------------

-- 顶点 1 没有出边
no-edge-from-one : ∀ {v : Fin 2} → edgeD (Fin.suc Fin.zero) v → ⊥
no-edge-from-one {Fin.zero}         ()
no-edge-from-one {Fin.suc Fin.zero} ()

-- 没有从 1 走到 0 的走（末边必须入 0，而唯一入 0 的边不存在）
no-walk-1-0 : Walk G-dag (Fin.suc Fin.zero) Fin.zero → ⊥
no-walk-1-0 (cons e p) = no-edge-from-one e

-- 从 0 出发的边只到 1，而从 1 回不来 ⇒ 「0 → … → 0」不可能
no-edge-from-zero : ∀ {v : Fin 2}
                  → edgeD Fin.zero v → Walk G-dag v Fin.zero → ⊥
no-edge-from-zero {Fin.zero}         () p
no-edge-from-zero {Fin.suc Fin.zero} tt p = no-walk-1-0 p

--------------------------------------------------------------------------------
-- §3. 唯一的闭走是空走
--------------------------------------------------------------------------------

closed-is-nil : ∀ (v : Fin 2) (w : Walk G-dag v v) → w ≡ nil v
closed-is-nil Fin.zero (nil .Fin.zero) = refl
closed-is-nil Fin.zero (cons e p) = ⊥-elim (no-edge-from-zero e p)
closed-is-nil (Fin.suc Fin.zero) (nil .(Fin.suc Fin.zero)) = refl
closed-is-nil (Fin.suc Fin.zero) (cons e p) = ⊥-elim (no-edge-from-one e)

--------------------------------------------------------------------------------
-- §4. π₁ᵈ(G-dag) 幂等
--------------------------------------------------------------------------------

-- 闭走与自身复合仍是它自己
++w-nil : ∀ {v : Fin 2} (w : Walk G-dag v v) → w ++w w ≡ w
++w-nil {v} w = trans (cong (w ++w_) (closed-is-nil v w)) (++w-identityʳ w)

-- ★ 幂等：`w · w ⁓ w`
pi1d-idempotent : ∀ (v : Fin 2) (w : Walk G-dag v v)
                → AHomotopy G-dag (w ++w w) w
pi1d-idempotent v w = ≡→AH (++w-nil w)

--------------------------------------------------------------------------------
-- §5. 但它不是完全有向图 ⇒ 猜想的 ⟹ 方向为假
--------------------------------------------------------------------------------

not-complete : ¬ (∀ (u v : Fin 2) → edge G-dag u v)
not-complete h = h Fin.zero Fin.zero
