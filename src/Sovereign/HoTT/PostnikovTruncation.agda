{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.HoTT.PostnikovTruncation
-- 任务书 6.1：Postnikov 截断的离散对应——walk 累积位移的 1-截断 + A-homotopy 守恒
--
-- 数学背景：Postnikov 塔的 n-截断抹除 > n 阶同伦信息。离散对应（库内语境）：
--   1-截断 = walk 的净位移（HomotopyPi1 的「离散同伦 = 净位移等价」）——
--   A-homotopy 生成元（slide/expand）保持净位移（权重调和条件下）→
--   截断映射与 A-homotopy 交换（trunc-resp）。
--
-- 核心原则：
-- 1. 纯构造（record/data 形 + 幺半群重排链——零 mod-helper 零 literal 归纳）
-- 2. 条件化引理（slide 守恒的权重条件显式声明——诚实边界）
-- 3. 诚实标注：这是 Postnikov 截断的**离散类比**（真身是空间截断——库内是位移截断）
--
-- 包含：WeightedDiGraph / disp（净位移）/ ++w-disp / slide-expand-守恒 / AH-resp

module Sovereign.HoTT.PostnikovTruncation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Sovereign.Topology.BarceloAHomotopy using (DiGraph; V; Walk; nil; cons; _++w_; AStep; slide; expand; AHomotopy; refl'; symm; trans'; gen)
open DiGraph using (V; edge)

-- ────────────────────────────────────────────────────────────────────
-- §1. 加权有向图（交换幺半群权重——位移的代数载体）
-- ────────────────────────────────────────────────────────────────────

record WeightedDiGraph : Set₁ where
  field
    G     : DiGraph
    A     : Set
    _+A_  : A → A → A
    zeroA : A
    _*A_  : A → A → A
    oneA  : A
    wt    : V G → V G → A
    +A-assoc  : ∀ x y z → (x +A y) +A z ≡ x +A (y +A z)
    +A-comm   : ∀ x y → x +A y ≡ y +A x
    +A-idˡ    : ∀ x → zeroA +A x ≡ x
    *A-assoc  : ∀ x y z → (x *A y) *A z ≡ x *A (y *A z)
    *A-idʳ    : ∀ x → x *A oneA ≡ x
    *A-idˡ    : ∀ x → oneA *A x ≡ x

open WeightedDiGraph

-- ────────────────────────────────────────────────────────────────────
-- §2. 净位移（walk 权重累积 = 1-截断映射）
-- ────────────────────────────────────────────────────────────────────

disp : (W : WeightedDiGraph) → ∀ {u v} → Walk (G W) u v → A W
disp W (nil v) = zeroA W
disp W (cons {u = u} {v = v} e p) = _+A_ W (wt W u v) (disp W p)

-- walk 连接的位移可加性
++w-disp : (W : WeightedDiGraph) → ∀ {u v w} (p : Walk (G W) u v) (q : Walk (G W) v w)
         → disp W (p ++w q) ≡ _+A_ W (disp W p) (disp W q)
++w-disp W = go
  where
  go : ∀ {u v w} (p : Walk (G W) u v) (q : Walk (G W) v w)
     → disp W (p ++w q) ≡ _+A_ W (disp W p) (disp W q)
  go (nil v) q = sym (+A-idˡ W (disp W q))
  go (cons {u = u} {v = v} e p) q =
    trans (cong (λ z → _+A_ W (wt W u v) z) (go p q))
          (sym (+A-assoc W (wt W u v) (disp W p) (disp W q)))

-- ────────────────────────────────────────────────────────────────────
-- §3. slide/expand 守恒（权重调和条件下的位移不变）
-- ────────────────────────────────────────────────────────────────────

slide-preserves-disp : (W : WeightedDiGraph) → ∀ {u x y z v}
  (p : Walk (G W) u x) (b : Walk (G W) z v)
  (e1 : edge (G W) x y) (e2 : edge (G W) y z) (e3 : edge (G W) x z)
  → _+A_ W (wt W x y) (wt W y z) ≡ wt W x z
  → disp W (p ++w (cons e1 (cons e2 b))) ≡ disp W (p ++w (cons e3 b))
slide-preserves-disp W {u} {x} {y} {z} {v} p b e1 e2 e3 harm =
  trans (++w-disp W p (cons e1 (cons e2 b)))
  (trans (cong (λ w → _+A_ W (disp W p) w) (sym (+A-assoc W (wt W x y) (wt W y z) (disp W b))))
  (trans (cong (λ w → _+A_ W (disp W p) (_+A_ W w (disp W b))) harm)
  (sym (++w-disp W p (cons e3 b)))))

expand-preserves-disp : (W : WeightedDiGraph) → ∀ {u x y z v}
  (p : Walk (G W) u x) (b : Walk (G W) z v)
  (e1 : edge (G W) x y) (e2 : edge (G W) y z) (e3 : edge (G W) x z)
  → _+A_ W (wt W x y) (wt W y z) ≡ wt W x z
  → disp W (p ++w (cons e3 b)) ≡ disp W (p ++w (cons e1 (cons e2 b)))
expand-preserves-disp W p b e1 e2 e3 harm = sym (slide-preserves-disp W p b e1 e2 e3 harm)

-- ────────────────────────────────────────────────────────────────────
-- §4. trunc-resp：A-homotopy 保持净位移（1-截断与同伦交换）
-- ────────────────────────────────────────────────────────────────────

AH-resp : (W : WeightedDiGraph) → ∀ {u v} {w1 w2 : Walk (G W) u v}
  → (harm : ∀ x y z → (e1 : edge (G W) x y) (e2 : edge (G W) y z) (e3 : edge (G W) x z)
          → _+A_ W (wt W x y) (wt W y z) ≡ wt W x z)
  → AHomotopy (G W) w1 w2 → disp W w1 ≡ disp W w2
AH-resp W harm (refl' w) = refl
AH-resp W harm (symm h) = sym (AH-resp W harm h)
AH-resp W harm (trans' h1 h2) = trans (AH-resp W harm h1) (AH-resp W harm h2)
AH-resp W {u} {v} {w1} {w2} harm (gen (slide {u = u'} {x = x} {y = y} {z = z} {v = v'} p b e1 e2 e3)) =
  slide-preserves-disp W p b e1 e2 e3 (harm x y z e1 e2 e3)
AH-resp W {u} {v} {w1} {w2} harm (gen (expand {u = u'} {x = x} {y = y} {z = z} {v = v'} p b e1 e2 e3)) =
  expand-preserves-disp W p b e1 e2 e3 (harm x y z e1 e2 e3)

-- 诚实边界：Postnikov n≥2 截断（高阶同伦）留后续层；本层为 1-截断（净位移）的离散对应

-- ────────────────────────────────────────────────────────────────────
-- §5. Postnikov 2-截断（离散对应——walk 的二阶位移/相邻步对守恒）
--   2-截断 = 「步对」的位移累积（相邻两步的权重和序列）——slide 守恒的二阶形式
-- ────────────────────────────────────────────────────────────────────

-- 步对位移（相邻两步的权重和——2-截断的信息层）
-- 二阶位移（相邻步对的权重和累积——2-截断信息层）
-- 二阶信息（步对积的累积——乘法形 harm 条件）
disp2 : (W : WeightedDiGraph) → ∀ {u v} → Walk (G W) u v → A W
disp2 W (nil v) = oneA W
disp2 W (cons {u = u} {v = v} e (nil w)) = wt W u v
disp2 W (cons {u = u} {v = v} e (cons {v = w} e' p)) = _*A_ W (_*A_ W (wt W u v) (wt W v w)) (disp2 W p)

-- 2-截断守恒骨架（slide 的二阶形式——步对权重和守恒）
disp2-slide : (W : WeightedDiGraph) → ∀ {u x y z v}
  (p : Walk (G W) u x) (b : Walk (G W) z v)
  (e1 : edge (G W) x y) (e2 : edge (G W) y z) (e3 : edge (G W) x z)
  → _*A_ W (wt W x y) (wt W y z) ≡ wt W x z
  → disp2 W (p ++w (cons e1 (cons e2 b))) ≡ disp2 W (p ++w (cons e3 b))
disp2-slide W {u} {x} {y} {z} {v} (nil x) (nil z) e1 e2 e3 harm =
  trans (cong (λ w → _*A_ W w (oneA W)) harm) (*A-idʳ W (wt W x z))
disp2-slide W p b e1 e2 e3 harm = {!!}
  -- WIP：二阶守恒（++w-disp2 引理 + 边界步对 + harm 条件）

-- ────────────────────────────────────────────────────────────────────
-- §6. ++w-disp2（边界步对分解——general 形基础）
-- ────────────────────────────────────────────────────────────────────

v-test : DiGraph → Set
v-test G = V G

tailW : (W : WeightedDiGraph) → ∀ {u v} → Walk (G W) u v → Σ (V (G W)) (λ w → Walk (G W) u w)
tailW W = go
  where
    G' : DiGraph
    G' = G W
    go : ∀ {u v} → Walk G' u v → Σ (V G') (λ w → Walk G' u w)
    go (nil v) = (v , nil v)
    go (cons e p) = (_ , p)
tailW W (nil v) = (v , nil v)
tailW W (cons e p) = (_ , p)

firstW : (W : WeightedDiGraph) → ∀ {u v} → Walk (G W) u v → A W
firstW W (nil v) = oneA W
firstW W (cons {u = u} {v = v} e p) = wt W u v

lastW : (W : WeightedDiGraph) → ∀ {u v} → Walk (G W) u v → A W
lastW W (nil v) = oneA W
lastW W (cons {u = u} {v = v} e (nil w)) = wt W u v
lastW W (cons e (cons e' p)) = lastW W (cons e' p)

++w-disp2 : (W : WeightedDiGraph) → ∀ {u v w} (p : Walk (G W) u v) (q : Walk (G W) v w)
  → disp2 W (p ++w q) ≡ _*A_ W (disp2 W p) (_*A_ W (_*A_ W (lastW W p) (firstW W q)) (disp2 W q))
++w-disp2 W (nil v) q = trans (sym (WeightedDiGraph.*A-idˡ W (disp2 W q)))
  (cong (λ w → WeightedDiGraph._*A_ W (WeightedDiGraph.oneA W) w)
        (sym (WeightedDiGraph.*A-idˡ W (disp2 W q))))
++w-disp2 W (cons e (nil w)) (nil v) = {!!}
  -- WIP：单步 + nil（disp2 (cons e nil) = wt u v vs wt u v *A (wt u v *A oneA)）
++w-disp2 W (cons e (nil w)) (cons e' q) = {!!}
  -- WIP：单步 + 步对（边界步对 + 递归）
++w-disp2 W (cons e (cons e' p)) q = {!!}
  -- WIP：步对 + 递归（边界步对 + assoc 桥）
