{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyNoCollapse
--
-- **裁决 2 步 4 的落地**：把一般图 π₁ᵈ 的结构判据当**引理**用在 Cayley 图上
--
-- ## 裁决之间的关系
--
-- | 裁决 | 内容 | 本模块 |
-- |---|---|---|
-- | 2 步 1–2 | `π₁ᵈ` 定义在 `T⁶ = (Z/3)ⁿ` 的 Cayley 图上 | 用 `T6CayleyVec` |
-- | **2 步 4** | **一般图的 `π₁ᵈ` 降为引理**（结构不变量保留） | **本模块就是这件事的示范** ✓ |
--
-- 本模块把 `Pi1dCardinality` 的 `no-collapse-iff-triangle-free`（一般图判据）
-- **当作引理**作用在 `T6CayleyVec 1` 上 —— 这既验证了裁决 2 步 4 的分层，
-- 又给出了一个关于**裁决指定的载体**的实质结论。
--
-- ## 结论
--
-- ```
--   T6CayleyVec 1 无有向三角形（tf1）
--   ⇒ NoCollapse（T6CayleyVec 1）：AHomotopy 退化为命题相等
--   ⇒ 该图上**任何两条不同的走都不同伦**，特别地「绕三圈」与「空走」不粘连
-- ```
--
-- **⇒ 裁决 2 第 3 步的「三步归零 ⇒ π₁ᵈ ≅ C₃」在这一载体上不成立**：
-- 三步回到的是**顶点**（`T6CayleyVec.cycWalk3Vec` 已证），但走层不塌缩。
-- 与 `Pi1dCycleThree` 在 `G3`（同一图的函数载体表述）上的结论一致 ✓
--
-- ## 为什么 `T6CayleyVec 1` 无三角形
--
-- `n = 1` 时只有一个生成元索引（`Fin 1` 唯一元素），所以边只有一种：
-- `x ↦ updAt 0 x`。三个顶点是 `[0] → [1] → [2] → [0]`。
-- 「三角形」要求 `[a] → [a+1] → [a+2]` 且同时 `[a] → [a+2]` ——
-- 但后者不存在：从 `[a]` 出发唯一的边到 `[a+1]`。
-- 形式化归约为 `succF3 (succF3 a) ≢ succF3 a`（`Fin 3` 三 case 穷举）✓
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · **不重证**一般判据 —— 直接 `open import` 后当引理用（裁决 2 步 4）

module Sovereign.Synthesis.Homotopy.T6CayleyNoCollapse where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Vec using (Vec; []; _∷_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Sovereign.Synthesis.Homotopy.T6CayleyGraph using (succF3)
open import Sovereign.Synthesis.Homotopy.T6CayleyVec
  using (updAt; updAt-cubed; T6CayleyVec; T6Vec;
         cycWalk3-open; cycWalk3Vec)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; nil; AHomotopy)
open import Sovereign.Synthesis.Homotopy.Pi1dCardinality
  using (TriangleFree; NoCollapse; no-collapse-iff-triangle-free; walk-len)
open import Data.Product using (Σ; proj₂; _,_)

--------------------------------------------------------------------------------
-- §1. 取首坐标（`Vec (Fin 3) 1` 只有一个坐标）
--------------------------------------------------------------------------------

headF3 : Vec (Fin 3) 1 → Fin 3
headF3 (a ∷ []) = a

--------------------------------------------------------------------------------
-- §2. `succF3` 走两步不等于走一步（Fin 3 三个 case）
--------------------------------------------------------------------------------

s2≢s : ∀ (a : Fin 3) → succF3 (succF3 a) ≡ succF3 a → ⊥
s2≢s Fin.zero                     ()
s2≢s (Fin.suc Fin.zero)           ()
s2≢s (Fin.suc (Fin.suc Fin.zero)) ()

--------------------------------------------------------------------------------
-- §3. ★ `T6CayleyVec 1` 无有向三角形
--------------------------------------------------------------------------------

-- `Fin 1` 的唯一元素，用于把生成元索引写清楚
only1 : Fin 1
only1 = Fin.zero

tf1 : TriangleFree (T6CayleyVec 1)
tf1 {a ∷ []} (Fin.zero , e1) (Fin.zero , e2) (Fin.zero , e3) =
  s2≢s a (cong headF3 (trans (cong (updAt Fin.zero) (sym e1))
                         (trans (sym e2) e3)))

--------------------------------------------------------------------------------
-- §4. ★ 引理复用：NoCollapse（AHomotopy 退化为命题相等）
--------------------------------------------------------------------------------

no-collapse-t1 : NoCollapse (T6CayleyVec 1)
no-collapse-t1 =
  proj₂ (no-collapse-iff-triangle-free {G = T6CayleyVec 1}) tf1

--------------------------------------------------------------------------------
-- §5. ★★ 「三步回不到空走」——在裁决指定的 Cayley 载体上直接陈述
--
-- `cycWalk3Vec` 是**真闭走**（三步回到顶点）；本节证它与**空走不同伦**。
-- 这就是「顶点层三步归零」与「走层塌缩」的分离点 ✓
--------------------------------------------------------------------------------

-- `subst` 不改变走长（沿端点等式搬运）
subst-len : ∀ {n : ℕ} (x : T6Vec n) {a b : T6Vec n}
            (eq : a ≡ b) (w : Walk (T6CayleyVec n) x a)
          → walk-len (subst (Walk (T6CayleyVec n) x) eq w) ≡ walk-len w
subst-len x refl w = refl

-- 真闭走的长度是 3
cyc3-len : ∀ (j : Fin 1) (x : T6Vec 1) → walk-len (cycWalk3Vec 1 j x) ≡ 3
cyc3-len j x =
  trans (subst-len x (updAt-cubed j x) (cycWalk3-open 1 j x)) refl

3≢0 : 3 ≡ 0 → ⊥
3≢0 ()

-- ★★ 三步走与空走**不同伦** ⇒ π₁ᵈ 里 g³ ≠ e ⇒ 不是 C₃
cyc3≢nil : ∀ (j : Fin 1) (x : T6Vec 1)
         → ¬ (AHomotopy (T6CayleyVec 1) (cycWalk3Vec 1 j x) (nil x))
cyc3≢nil j x ah =
  3≢0 (trans (sym (cyc3-len j x)) (cong walk-len (no-collapse-t1 ah)))
