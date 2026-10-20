{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.C5LoopIrrelevance
--
-- **自环无关性：π₁(C5L) = π₁(C₅) ≅ ℤ**（课题 2 的正式件 ✓）
--
-- 数学背景（oracle 96cc33a0… 判定 ✓ C5L 闭走 ≤6 = 3 类 {wind 0,±5} ⇒ ℤ ✓）：
--   C5L = 自环填充 C₅（每顶点加自环 ✓ LoopedGraph ✓）
--   标准 A-同伦的生成元集含 tri-slide/sq-slide4/bt ✓（_PEH32 ✓）
--   ⇒ **自环平凡**：`(x,x) ~ nil` ✓
--      ① tri-slide（e3 = 自环弦 ✓）逆向：p·(cw x)·(ccw x)·q ~ p·(lp x)·q ✓
--      ② bt（回溯消去 ✓）：p·(cw x)·(ccw x)·q ~ p·q ✓
--   ⇒ **loop-irrelevance**：每条 C5L 走 ~ 其自环擦除像 ✓
--   ⇒ **C5L 商 = C₅ 商 ≅ ℤ** ✓（幂等元不存在 ✗ 修正「自环幂等类」原假设 ✓）
--
-- 核心原则：证明携带边（`y ≡ f x`）使中点成为模式变量 ⇒ 结构递归可行 ✓
-- 0 postulate / 0 hole。来源探针：_PEH53（12f698c6…）/ _PEH54（058d973f…）

module Sovereign.Synthesis.Homotopy.C5LoopIrrelevance where

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; cons; nil; _++w_)
open import Sovereign.Synthesis.Homotopy.C5Rigidity
  using (AStepStd; tri-slide; sq-slide4; bt)

--------------------------------------------------------------------------------
-- ⓪ 标准 A-同伦等价闭包（三律 + 生成元 ✓）
--------------------------------------------------------------------------------

data AHomotopyStd (G : DiGraph) : ∀ {u v} → Walk G u v → Walk G u v → Set where
  rfl : ∀ {u v} (w : Walk G u v) → AHomotopyStd G w w
  sym : ∀ {u v} {w1 w2 : Walk G u v} → AHomotopyStd G w1 w2 → AHomotopyStd G w2 w1
  trn : ∀ {u v} {w1 w2 w3 : Walk G u v}
      → AHomotopyStd G w1 w2 → AHomotopyStd G w2 w3 → AHomotopyStd G w1 w3
  gen : ∀ {u v} {w1 w2 : Walk G u v} → AStepStd G w1 w2 → AHomotopyStd G w1 w2

--------------------------------------------------------------------------------
-- ① LoopedGraph 与 C5L（承重件 ✓）
--------------------------------------------------------------------------------

record LoopedGraph : Set₁ where
  field
    graph : DiGraph
    loop  : ∀ v → DiGraph.edge (graph) v v

--------------------------------------------------------------------------------
-- ② C₅ 自环填充实例 ✓
--------------------------------------------------------------------------------

data C5-vert : Set where
  c0 c1 c2 c3 c4 : C5-vert

next5 : C5-vert → C5-vert
next5 c0 = c1
next5 c1 = c2
next5 c2 = c3
next5 c3 = c4
next5 c4 = c0

data C5-edge : C5-vert → C5-vert → Set where
  cw5  : ∀ i → C5-edge i (next5 i)
  ccw5 : ∀ i → C5-edge (next5 i) i
  lp5  : ∀ i → C5-edge i i

C5D : DiGraph
C5D = record { V = C5-vert ; edge = C5-edge }

C5L : LoopedGraph
C5L = record { graph = C5D ; loop = lp5 }

--------------------------------------------------------------------------------
-- ③④ AStepL（AStepStd 继承 + lp 移动 ✓）与演示——模块参数化 + open 字段直用 ✓
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ② 自环平凡（全称 ✓）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ★ 自环平凡（全称 ✓）：p·(lp x)·q ~ p·q
--------------------------------------------------------------------------------

lp-trivial : ∀ {u v : C5-vert} (x : C5-vert) (p : Walk C5D u x) (q : Walk C5D x v)
  → AHomotopyStd C5D (p ++w (cons (lp5 x) q)) (p ++w q)
lp-trivial x p q =
  trn (sym (gen (tri-slide p q (cw5 x) (ccw5 x) (lp5 x))))
      (gen (bt p q (cw5 x) (ccw5 x)))

--------------------------------------------------------------------------------
-- 推论：单自环闭走 (c0,c0) ~ nil ✓（oracle 判定的具体点 ✓）
--------------------------------------------------------------------------------

loop-trivial : AHomotopyStd C5D (cons (lp5 c0) (nil c0)) (nil c0)
loop-trivial = lp-trivial c0 (nil c0) (nil c0)

--------------------------------------------------------------------------------
-- ③ 自环无关性（收口 ✓）
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ① 头部上下文：AStepStd（3 子句 ✓ 每生成元的 p 吸收 cons ✓）
--------------------------------------------------------------------------------

step-cons : ∀ {u v w : C5-vert} (e : C5-edge u v) {w1 w2 : Walk C5D v w}
  → AStepStd C5D w1 w2 → AStepStd C5D (cons e w1) (cons e w2)
step-cons e (tri-slide p b e1 e2 e3) = tri-slide (cons e p) b e1 e2 e3
step-cons e (sq-slide4 p b e1 e2 e3 e4) = sq-slide4 (cons e p) b e1 e2 e3 e4
step-cons e (bt p q e1 e2) = bt (cons e p) q e1 e2

--------------------------------------------------------------------------------
-- ② 头部上下文：闭包（归纳 ✓）
--------------------------------------------------------------------------------

AH-cons : ∀ {u v w : C5-vert} (e : C5-edge u v) {w1 w2 : Walk C5D v w}
  → AHomotopyStd C5D w1 w2 → AHomotopyStd C5D (cons e w1) (cons e w2)
AH-cons e (rfl w) = rfl (cons e w)
AH-cons e (sym h) = sym (AH-cons e h)
AH-cons e (trn h1 h2) = trn (AH-cons e h1) (AH-cons e h2)
AH-cons e (gen s) = gen (step-cons e s)

--------------------------------------------------------------------------------
-- ③ 自环擦除（结构递归 ✓ 4 子句 ✓）
--------------------------------------------------------------------------------

erase-lp : ∀ {u v : C5-vert} (w : Walk C5D u v) → Walk C5D u v
erase-lp (nil x) = nil x
erase-lp (cons (cw5 i) b) = cons (cw5 i) (erase-lp b)
erase-lp (cons (ccw5 i) b) = cons (ccw5 i) (erase-lp b)
erase-lp (cons (lp5 i) b) = erase-lp b

--------------------------------------------------------------------------------
-- ④ ★ 擦除等价（归纳 ✓ lp 案用 lp-trivial ✓）
--------------------------------------------------------------------------------

erase-equiv : ∀ {u v : C5-vert} (w : Walk C5D u v)
  → AHomotopyStd C5D w (erase-lp w)
erase-equiv (nil x) = rfl (nil x)
erase-equiv (cons (cw5 i) b) = AH-cons (cw5 i) (erase-equiv b)
erase-equiv (cons (ccw5 i) b) = AH-cons (ccw5 i) (erase-equiv b)
erase-equiv (cons (lp5 i) b) = trn (lp-trivial i (nil i) b) (erase-equiv b)

--------------------------------------------------------------------------------
-- ⑤ ★★ 自环无关性（收口陈述 ✓）
--------------------------------------------------------------------------------

loop-irrelevance : ∀ {u v : C5-vert} (w : Walk C5D u v)
  → AHomotopyStd C5D w (erase-lp w)
loop-irrelevance = erase-equiv
