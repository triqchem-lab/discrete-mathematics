{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi1dMonoid
--
-- **π₁ᵈ(G) 的一般理论**：对**任意**有向图 G，闭走模 A-同伦构成**幺半群**。
--
-- ## 数学背景
--
-- Barcelo A-同伦（`BarceloAHomotopy`）把「走」`Walk G u v` 按 `AStep` 生成的等价闭包
-- `AHomotopy` 分类。对固定的基点 v，**闭走模 A-同伦** `π₁ᵈ(G) := Walk G v v / AHomotopy`
-- 带连接运算 `_++w_`。
--
-- **一般定理（本模块）**：
--   ① `_++w_` 关于 `AHomotopy` **良定义**（左同余 + 右同余）
--   ② 单位律（`nil v`）
--   ③ 结合律
--   ⇒ **π₁ᵈ(G) 是幺半群** ✓
--
-- ⚠ **不一定是群** ✗ —— 反例是库内既有的 `PIO-1.card-divergence`：
--   `Gcmp two-chain` 的 π₁ᵈ 是**2 元幂等幺半群**（非群 ✗）。
--   ⇒ 「一般理论」的正确形态是**幺半群** ✓，不是群 ✗。
--
-- ## ★ 关键技术要点（2026-10-21 修正）
--
-- `_++w_` 按**第一参数**递归：
--   ```
--   nil v      ++w q = q
--   cons e p'  ++w q = cons e (p' ++w q)
--   ```
-- ⇒ 左单位是定义性相等 ✓，但 `(p ++w q) ++w r ≡ p ++w (q ++w r)` 对任意 `p`
--   **不是**定义性相等（Agda 定义相等不做归纳）⇒ 必须用 `++w-assoc` + `subst` ✗
--   （初版误判为「右同余定义性」，编译期已被证伪，此处保留记录）。
--
-- ## 核心原则
--   · 对**任意** `DiGraph` 成立（不依赖具体图）✓
--   · 0 postulate / 0 hole
--   · 复用 `BarceloAHomotopy` 的 `DiGraph`/`Walk`/`AStep`/`AHomotopy`（只 import ✓）

module Sovereign.Synthesis.Homotopy.Pi1dMonoid where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AStep; slide; expand;
         AHomotopy; refl'; symm; trans'; gen;
         AH-refl; AH-symm; AH-trans; AStep⊆AH)

--------------------------------------------------------------------------------
-- §1. `_++w_` 的代数律
--------------------------------------------------------------------------------

-- ① 右单位：`w ++w nil ≡ w`
++w-identityʳ : ∀ {G : DiGraph} {u v} (w : Walk G u v) → w ++w nil v ≡ w
++w-identityʳ (nil v)      = refl
++w-identityʳ (cons e p)   = cong (cons e) (++w-identityʳ p)

-- ② 左单位（按第一参数递归 ⇒ 定义性相等）
++w-identityˡ : ∀ {G : DiGraph} {u v} (w : Walk G u v) → nil u ++w w ≡ w
++w-identityˡ w = refl

-- ③ 结合律
++w-assoc : ∀ {G : DiGraph} {u v w x}
            (p : Walk G u v) (q : Walk G v w) (r : Walk G w x)
          → (p ++w q) ++w r ≡ p ++w (q ++w r)
++w-assoc (nil v)      q r = refl
++w-assoc (cons e p)   q r = cong (cons e) (++w-assoc p q r)

--------------------------------------------------------------------------------
-- §2. AStep 的左右同余
--------------------------------------------------------------------------------

-- 二元 `subst`（stdlib 的 `subst₂` 形状不同，这里只要最朴素的版本）
subst₂-AStep : ∀ {G : DiGraph} {u v} {a a' b b' : Walk G u v}
             → a ≡ a' → b ≡ b' → AStep G a b → AStep G a' b'
subst₂-AStep refl refl z = z

-- ④ AStep 的右同余：在 `p` 之后插一步替换，`b ↦ b ++w r`
AStep-++w : ∀ {G : DiGraph} {u v w} {p q : Walk G u v}
            (r : Walk G v w)
          → AStep G p q → AStep G (p ++w r) (q ++w r)
AStep-++w r (slide  p b e1 e2 e3) =
  subst₂-AStep (sym (++w-assoc p (cons e1 (cons e2 b)) r))
               (sym (++w-assoc p (cons e3 b) r))
               (slide p (b ++w r) e1 e2 e3)
AStep-++w r (expand p b e1 e2 e3) =
  subst₂-AStep (sym (++w-assoc p (cons e3 b) r))
               (sym (++w-assoc p (cons e1 (cons e2 b)) r))
               (expand p (b ++w r) e1 e2 e3)

-- ⑤ AStep 的左同余：在 `p` 之前插一步替换
AStep-++wˡ : ∀ {G : DiGraph} {u v w} {p q : Walk G v w}
             (r : Walk G u v)
           → AStep G p q → AStep G (r ++w p) (r ++w q)
AStep-++wˡ r (slide  p b e1 e2 e3) =
  subst₂-AStep (++w-assoc r p (cons e1 (cons e2 b)))
               (++w-assoc r p (cons e3 b))
               (slide (r ++w p) b e1 e2 e3)
AStep-++wˡ r (expand p b e1 e2 e3) =
  subst₂-AStep (++w-assoc r p (cons e3 b))
               (++w-assoc r p (cons e1 (cons e2 b)))
               (expand (r ++w p) b e1 e2 e3)

-- ⑥ AHomotopy 的右同余（等价闭包四案归纳）
AH-++w : ∀ {G : DiGraph} {u v w} {p q : Walk G u v}
         (r : Walk G v w)
       → AHomotopy G p q → AHomotopy G (p ++w r) (q ++w r)
AH-++w r (refl' p)      = refl' (p ++w r)
AH-++w r (symm h)       = symm (AH-++w r h)
AH-++w r (trans' h1 h2) = trans' (AH-++w r h1) (AH-++w r h2)
AH-++w r (gen st)       = gen (AStep-++w r st)

-- ⑦ AHomotopy 的左同余
AH-++wˡ : ∀ {G : DiGraph} {u v w} {p q : Walk G v w}
          (r : Walk G u v)
        → AHomotopy G p q → AHomotopy G (r ++w p) (r ++w q)
AH-++wˡ r (refl' p)      = refl' (r ++w p)
AH-++wˡ r (symm h)       = symm (AH-++wˡ r h)
AH-++wˡ r (trans' h1 h2) = trans' (AH-++wˡ r h1) (AH-++wˡ r h2)
AH-++wˡ r (gen st)       = gen (AStep-++wˡ r st)

-- ⑧ 乘法同余（左右合并）—— `_++w_` 在 `AHomotopy` 上良定义
++w-cong : ∀ {G : DiGraph} {u v w}
           {p p' : Walk G u v} {q q' : Walk G v w}
         → AHomotopy G p p' → AHomotopy G q q'
         → AHomotopy G (p ++w q) (p' ++w q')
++w-cong {G = G} {q = q} {q' = q'} h1 h2 =
  AH-trans (AH-++w q h1) (AH-++wˡ _ h2)
