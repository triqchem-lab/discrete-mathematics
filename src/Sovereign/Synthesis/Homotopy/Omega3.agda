{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Omega3
--
-- **`Ω³` 定义层正式化** —— 第六层提升批 2（承接 `Omega2`）
--
-- ## 内容（定义逐字取自 `probes/_PPI5f:40-58`）
--
-- | 项 | 内容 |
-- |---|---|
-- | `invAStep` | `ASTep` 的方向反转（`slide` ↔ `expand`）✓ 对合 |
-- | `Ω3Step` | 3-步生成元：**唯一一条** `fill-tri`（三角面填充 = 2-圈的 3-消去）|
-- | `Ω3Walk` | 3-腔 = `Ω3Step` 的等价闭包（三律 + 生成元，与 `AHomotopy`/`AHomotopyStd` 同款模板）|
-- | `Ω3ᵈ` | 常值基点处的闭 3-走 `Ω3Walk G x (nil2 (nil x)) (nil2 (nil x))` |
--
-- ## 本模块证的（都是**定义层直接推论**，如实标注：不是计算）
--
-- | 引理 | 内容 |
-- |---|---|
-- | `invAStep-invol` | `invAStep (invAStep s) ≡ s`（对合）|
-- | `Ω3ᵈ-inhabited` | `Ω3ᵈ G x` **可居留**（见证 `refl3 (nil2 (nil x))`）|
-- | `Ω3-refl` / `Ω3-symm` / `Ω3-trans` | `Ω3Walk` 是**等价关系**（三律由构造子直接给出 ⇒ 零新公理）|
--
-- ## ⚠ 本模块**不**包含（如实标注）
--
--   · 扩展生成集 `Ω3Walk⁺`（`bub3` / `whisk3`，在 `_PPI5g`）—— 提升批 3；
--   · 商 `π₂ᵈ = Ω2Walk / Ω3Walk` —— 提升批 4（需裁 Cubical `_/_` vs 库内商型）；
--   · **任何计算**：`π₂ᵈ` 的群结构、非平凡实例都不在本模块。
--
-- ## 迭代模式的模板（`_PPI5d:54-57` 的原话，本模块是它的第 2 层实例）
--
-- ```
--   Ω¹ᵈ = Walk(V, edge)(x,x)
--   Ω²ᵈ = Walk(Walk, AStep)(nil, nil)
--   Ω³ᵈ = Walk(Ω2Walk, Ω3Step)(nil2, nil2)
--   …每阶载体 = 上阶闭走，步关系 = 上阶同伦生成元
-- ```
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `Omega2` 的 `Ω2Walk` / `nil2` / `cons2`（不重证）

module Sovereign.Synthesis.Homotopy.Omega3 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; AStep; slide; expand)
open DiGraph using (V)
open import Sovereign.Synthesis.Homotopy.Omega2
  using (Ω2Walk; nil2; cons2)

--------------------------------------------------------------------------------
-- §1. `ASTep` 的方向反转（对合）
--------------------------------------------------------------------------------

-- ⚠ `ASTep` 的索引是**走**（`Walk G u v`），不是顶点
invAStep : ∀ {G : DiGraph} {u v : V G} {p q : Walk G u v} → AStep G p q → AStep G q p
invAStep (slide  p b e1 e2 e3) = expand p b e1 e2 e3
invAStep (expand p b e1 e2 e3) = slide  p b e1 e2 e3

invAStep-invol : ∀ {G : DiGraph} {u v : V G} {p q : Walk G u v} (s : AStep G p q)
               → invAStep (invAStep s) ≡ s
invAStep-invol (slide  p b e1 e2 e3) = refl
invAStep-invol (expand p b e1 e2 e3) = refl

--------------------------------------------------------------------------------
-- §2. `Ω3Step`：3-步生成元（唯一一条 `fill-tri`）
--
-- 语义：2-腔「先滑后展」(`s ∘ s⁻¹`) 的三角面可 3-缩至平凡 2-腔。
-- 这是 3-腔的**本体数据** —— 不是我们额外加的，是「填充」这件事本身。
--------------------------------------------------------------------------------

data Ω3Step (G : DiGraph) (x : V G)
  : {w1 w2 : Walk G x x} → Ω2Walk G x w1 w2 → Ω2Walk G x w1 w2 → Set where
  fill-tri : {w1 w2 : Walk G x x} (s : AStep G w1 w2)
           → Ω3Step G x (cons2 s (cons2 (invAStep s) (nil2 w1))) (nil2 w1)

--------------------------------------------------------------------------------
-- §3. `Ω3Walk`：3-腔 = `Ω3Step` 的等价闭包（三律 + 生成元）
--------------------------------------------------------------------------------

data Ω3Walk (G : DiGraph) (x : V G)
  : {w1 w2 : Walk G x x} → Ω2Walk G x w1 w2 → Ω2Walk G x w1 w2 → Set where
  refl3  : {w1 w2 : Walk G x x} (c : Ω2Walk G x w1 w2) → Ω3Walk G x c c
  symm3  : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
         → Ω3Walk G x c c' → Ω3Walk G x c' c
  trans3 : {w1 w2 : Walk G x x} {c1 c2 c3 : Ω2Walk G x w1 w2}
         → Ω3Walk G x c1 c2 → Ω3Walk G x c2 c3 → Ω3Walk G x c1 c3
  gen3   : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
         → Ω3Step G x c c' → Ω3Walk G x c c'

-- `Ω³ᵈ`：常值基点处的闭 3-走
Ω3ᵈ : (G : DiGraph) → V G → Set
Ω3ᵈ G x = Ω3Walk G x (nil2 (nil x)) (nil2 (nil x))

--------------------------------------------------------------------------------
-- §4. 定义层的直接推论（**都不是计算**，如实标注）
--------------------------------------------------------------------------------

-- `Ω³ᵈ` 可居留
Ω3ᵈ-inhabited : ∀ {G : DiGraph} {x : V G} → Ω3ᵈ G x
Ω3ᵈ-inhabited = refl3 (nil2 (nil _))

-- `Ω3Walk` 是等价关系 —— 三律全部由构造子直接给出 ⇒ **零新公理**
Ω3-refl : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
          (c : Ω2Walk G x w1 w2) → Ω3Walk G x c c
Ω3-refl = refl3

Ω3-symm : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
          {c c' : Ω2Walk G x w1 w2} → Ω3Walk G x c c' → Ω3Walk G x c' c
Ω3-symm = symm3

Ω3-trans : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
           {c1 c2 c3 : Ω2Walk G x w1 w2}
         → Ω3Walk G x c1 c2 → Ω3Walk G x c2 c3 → Ω3Walk G x c1 c3
Ω3-trans = trans3
