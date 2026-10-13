{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.PostnikovTruncation
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

module Sovereign.Synthesis.PostnikovTruncation where

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

-- ────────────────────────────────────────────────────────────────────
-- disp2 不变量三件套（2026-10-10 清洞批）：disp2 = 全权积（up to *A-assoc）
--   prodW = 逐步乘积；prod-++w = 乘法分配（++w-disp 的 *A 对应）；disp2-prod = 两形等价
-- ────────────────────────────────────────────────────────────────────

prodW : (W : WeightedDiGraph) → ∀ {u v} → Walk (G W) u v → A W
prodW W (nil v) = oneA W
prodW W (cons {u = u} {v = v} e p) = _*A_ W (wt W u v) (prodW W p)

prod-++w : (W : WeightedDiGraph) → ∀ {u v w} (p : Walk (G W) u v) (q : Walk (G W) v w)
         → prodW W (p ++w q) ≡ _*A_ W (prodW W p) (prodW W q)
prod-++w W = go
  where
    go : ∀ {u v w} (p : Walk (G W) u v) (q : Walk (G W) v w)
       → prodW W (p ++w q) ≡ _*A_ W (prodW W p) (prodW W q)
    go (nil v) q = sym (*A-idˡ W (prodW W q))
    go (cons {u = u} {v = v} e p) q =
      trans (cong (_*A_ W (wt W u v)) (go p q))
            (sym (*A-assoc W (wt W u v) (prodW W p) (prodW W q)))

disp2-prod : (W : WeightedDiGraph) → ∀ {u v} (p : Walk (G W) u v) → disp2 W p ≡ prodW W p
disp2-prod W (nil v) = refl
disp2-prod W (cons {u = u} {v = v} e (nil w)) = sym (*A-idʳ W (wt W u v))
disp2-prod W (cons {u = u} {v = v} e (cons {v = w} e' p)) =
  trans (cong (_*A_ W (_*A_ W (wt W u v) (wt W v w))) (disp2-prod W p))
        (*A-assoc W (wt W u v) (wt W v w) (prodW W p))

-- 2-截断守恒骨架（slide 的二阶形式——步对权重和守恒）
disp2-slide : (W : WeightedDiGraph) → ∀ {u x y z v}
  (p : Walk (G W) u x) (b : Walk (G W) z v)
  (e1 : edge (G W) x y) (e2 : edge (G W) y z) (e3 : edge (G W) x z)
  → _*A_ W (wt W x y) (wt W y z) ≡ wt W x z
  → disp2 W (p ++w (cons e1 (cons e2 b))) ≡ disp2 W (p ++w (cons e3 b))

-- 泛化 harm（递归调用需要）
disp2-slide-gen : (W : WeightedDiGraph) → ∀ {u x y z v}
  (p : Walk (G W) u x) (b : Walk (G W) z v)
  (e1 : edge (G W) x y) (e2 : edge (G W) y z) (e3 : edge (G W) x z)
  → (∀ a b c → _*A_ W (wt W a b) (wt W b c) ≡ wt W a c)
  → disp2 W (p ++w (cons e1 (cons e2 b))) ≡ disp2 W (p ++w (cons e3 b))
disp2-slide-gen W {u} {x} {y} {z} {v} p b e1 e2 e3 harm-gen = trans left-half right-half
  where
    left-half : disp2 W (p ++w (cons e1 (cons e2 b)))
              ≡ _*A_ W (prodW W p) (_*A_ W (wt W x z) (prodW W b))
    left-half = trans (disp2-prod W (p ++w (cons e1 (cons e2 b))))
      (trans (prod-++w W p (cons e1 (cons e2 b)))
      (trans (cong (_*A_ W (prodW W p)) (sym (*A-assoc W (wt W x y) (wt W y z) (prodW W b))))
      (cong (λ w → _*A_ W (prodW W p) (_*A_ W w (prodW W b))) (harm-gen x y z))))
    right-half : _*A_ W (prodW W p) (_*A_ W (wt W x z) (prodW W b))
               ≡ disp2 W (p ++w (cons e3 b))
    right-half = sym (trans (disp2-prod W (p ++w (cons e3 b))) (prod-++w W p (cons e3 b)))

disp2-slide W {u} {x} {y} {z} {v} p b e1 e2 e3 harm = trans left-half right-half
  where
    left-half : disp2 W (p ++w (cons e1 (cons e2 b)))
              ≡ _*A_ W (prodW W p) (_*A_ W (wt W x z) (prodW W b))
    left-half = trans (disp2-prod W (p ++w (cons e1 (cons e2 b))))
      (trans (prod-++w W p (cons e1 (cons e2 b)))
      (trans (cong (_*A_ W (prodW W p)) (sym (*A-assoc W (wt W x y) (wt W y z) (prodW W b))))
      (cong (λ w → _*A_ W (prodW W p) (_*A_ W w (prodW W b))) harm)))
    right-half : _*A_ W (prodW W p) (_*A_ W (wt W x z) (prodW W b))
               ≡ disp2 W (p ++w (cons e3 b))
    right-half = sym (trans (disp2-prod W (p ++w (cons e3 b))) (prod-++w W p (cons e3 b)))

-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- ──── 线3 disp2-respects ────
-- Postnikov 2-截断：disp2 的 A-homotopy 不变量提升
-- 设计：主件 AHomotopy 归纳四案（refl/symm/trans'/gen）+ 辅件 AStep 二案
--       （slide = disp2-slide-gen 直调 / expand = sym 同件）。
-- 关键约束：harm 参数取**全局 gen 形**（∀ a b c → wt a b *A wt b c ≡ wt a c）
--          ——IH 间传递需要（symm/trans' 案的 IH 复用必须有全域 harm）。
-- ────────────────────────────────────────────────────────────────────

-- 辅件：步级不变量（AStep 二案）
--   slide  案 = disp2-slide-gen 直调（p·(x→y)(y→z)·b ⟶ p·(x→z)·b，harm x y z 代入）
--   expand 案 = 同件的 sym（反向步）
step-respects : (W : WeightedDiGraph) → ∀ {u v} {w1 w2 : Walk (G W) u v}
  (s : AStep (G W) w1 w2)
  (harm : ∀ a b c → _*A_ W (wt W a b) (wt W b c) ≡ wt W a c)
  → disp2 W w1 ≡ disp2 W w2
step-respects W (slide p b e1 e2 e3) harm = disp2-slide-gen W p b e1 e2 e3 harm
step-respects W (expand p b e1 e2 e3) harm = sym (disp2-slide-gen W p b e1 e2 e3 harm)

-- 主件：AHomotopy 归纳四案
--   refl'  案 = refl（defeq：disp2 W w ≡ disp2 W w）
--   symm   案 = sym ∘ IH（反向同伦 ⇒ 反向等式）
--   trans' 案 = trans ∘ IH 两连（同伦复合 ⇒ 等式传递）
--   gen    案 = 归约步级 step-respects
disp2-respects : (W : WeightedDiGraph) → ∀ {u v} {w1 w2 : Walk (G W) u v}
  (h : AHomotopy (G W) w1 w2)
  (harm : ∀ a b c → _*A_ W (wt W a b) (wt W b c) ≡ wt W a c)
  → disp2 W w1 ≡ disp2 W w2
disp2-respects W (refl' w) harm = refl
disp2-respects W (symm h) harm = sym (disp2-respects W h harm)
disp2-respects W (trans' h1 h2) harm = trans (disp2-respects W h1 harm) (disp2-respects W h2 harm)
disp2-respects W (gen s) harm = step-respects W s harm
