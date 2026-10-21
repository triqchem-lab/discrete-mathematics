{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Omega3Plus
--
-- **`Ω3Walk⁺`（扩展生成集）正式化 + `embed3` 桥** —— 第六层提升批 3
--
-- ## 内容（定义逐字取自 `probes/_PPI5g:40-65`）
--
-- | 项 | 内容 |
-- |---|---|
-- | `bub` | **气泡**：`s ∘ s⁻¹` 的边界 2-圈（组合形）|
-- | `Ω3Step⁺` | 扩展 3-步生成集：`base3+`（嵌入原 `Ω3Step`）+ `whisk3`（前缀缘饰）+ `bub3`（**任意位**气泡消去）|
-- | `Ω3Walk⁺` | 三律 + 生成元的闭包 |
-- | **`embed3`** | ★ **桥**：`Ω3Walk ⊆ Ω3Walk⁺`（细关系嵌入粗关系）|
--
-- ## 为什么 `embed3` 重要
--
-- 两个商的关系是**粗化**方向：
--
-- ```
--   π₂ᵈ  = Ω2Walk / Ω3Walk      （细商）
--   π₂ᵈ⁺ = Ω2Walk / Ω3Walk⁺     （粗商）
--   Ω3Walk ⊆ Ω3Walk⁺ ⇒ π₂ᵈ → π₂ᵈ⁺  （细商 → 粗商，良定义）
-- ```
--
-- `_PPI5j:90-93` 把这个下降映射写成「桥」。`embed3` 就是它的**关系层前提** ✓
--
-- ## 为什么 `bub3` 是「扩展」而不是「新公理」
--
-- `Δ³ = s ∘ s⁻¹` 是**可缩**的（先滑后展再滑，三角面填两次）。
-- `bub3` 把它**在任意上下文里**消去；而 `fill-tri`（原生成集）只在**前缀**位置消去
-- ⇒ `bub3` 补的是「位置无关性」，语义上仍由 `fill-tri` 的几何实在性支撑，
-- 不是凭空加的关系（探针 `_PPI5g` 的 §「生成集完备形」即此意）。
--
-- ## ⚠ 本模块**不**包含（如实标注）
--
--   · **`Ω3Walk⁺ → Ω3Walk`（反向包含）** —— 探针 `_PEH5:151` 明确记为本方向的
--     **未证**边界（「反向 = 细商扩展的完备性」）⇒ 粗化**不是**等价，是单向 ✓
--   · 商 `π₂ᵈ` / `π₂ᵈ⁺` —— 提升批 4（需裁 Cubical `_/_` vs 库内商型）
--   · 任何计算
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `Omega2` 的 `_++2_` / `nil2` / `cons2`、`Omega3` 的 `Ω3Step` / `Ω3Walk`（不重证）

module Sovereign.Synthesis.Homotopy.Omega3Plus where

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; AStep)
open DiGraph using (V)
open import Sovereign.Synthesis.Homotopy.Omega2
  using (Ω2Walk; nil2; cons2; _++2_)
open import Sovereign.Synthesis.Homotopy.Omega3
  using (invAStep; Ω3Step; Ω3Walk; refl3; symm3; trans3; gen3; fill-tri)

--------------------------------------------------------------------------------
-- §1. 气泡：`s ∘ s⁻¹` 的边界 2-圈
--------------------------------------------------------------------------------

bub : ∀ {G : DiGraph} {x : V G} {w w' : Walk G x x}
    → AStep G w w' → Ω2Walk G x w w
bub s = cons2 s (cons2 (invAStep s) (nil2 _))

--------------------------------------------------------------------------------
-- §2. 扩展 3-步生成集 `Ω3Step⁺`
--------------------------------------------------------------------------------

data Ω3Step⁺ (G : DiGraph) (x : V G)
  : {w1 w2 : Walk G x x} → Ω2Walk G x w1 w2 → Ω2Walk G x w1 w2 → Set where

  -- 原生成集嵌入
  base3+ : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
         → Ω3Step G x c c' → Ω3Step⁺ G x c c'

  -- 前缀缘饰：3-步在左乘下稳定
  whisk3 : {w1 wm w2 : Walk G x x} (c₁ : Ω2Walk G x w1 wm)
           {c c' : Ω2Walk G x wm w2}
         → Ω3Step⁺ G x c c' → Ω3Step⁺ G x (c₁ ++2 c) (c₁ ++2 c')

  -- **任意位**气泡消去（`fill-tri` 只做前缀位；`bub3` 补位置无关性）
  bub3   : {w1 wm w2 : Walk G x x} (c₁ : Ω2Walk G x w1 wm) {wm' : Walk G x x}
           (s : AStep G wm wm') (c₂ : Ω2Walk G x wm w2)
         → Ω3Step⁺ G x ((c₁ ++2 bub s) ++2 c₂) (c₁ ++2 c₂)

--------------------------------------------------------------------------------
-- §3. `Ω3Walk⁺`：扩展生成集的等价闭包
--------------------------------------------------------------------------------

data Ω3Walk⁺ (G : DiGraph) (x : V G)
  : {w1 w2 : Walk G x x} → Ω2Walk G x w1 w2 → Ω2Walk G x w1 w2 → Set where
  refl3+  : {w1 w2 : Walk G x x} (c : Ω2Walk G x w1 w2) → Ω3Walk⁺ G x c c
  symm3+  : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
          → Ω3Walk⁺ G x c c' → Ω3Walk⁺ G x c' c
  trans3+ : {w1 w2 : Walk G x x} {c1 c2 c3 : Ω2Walk G x w1 w2}
          → Ω3Walk⁺ G x c1 c2 → Ω3Walk⁺ G x c2 c3 → Ω3Walk⁺ G x c1 c3
  gen3+   : {w1 w2 : Walk G x x} {c c' : Ω2Walk G x w1 w2}
          → Ω3Step⁺ G x c c' → Ω3Walk⁺ G x c c'

--------------------------------------------------------------------------------
-- §4. ★ `embed3`：细关系嵌入粗关系（批 4 的下降映射的关系层前提）
--------------------------------------------------------------------------------

embed3 : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
         {c c' : Ω2Walk G x w1 w2}
       → Ω3Walk G x c c' → Ω3Walk⁺ G x c c'
embed3 (refl3 c)      = refl3+ c
embed3 (symm3 h)      = symm3+ (embed3 h)
embed3 (trans3 h1 h2) = trans3+ (embed3 h1) (embed3 h2)
embed3 (gen3 st)      = gen3+ (base3+ st)

--------------------------------------------------------------------------------
-- §5. `Ω3Walk⁺` 是等价关系（三律由构造子直接给出 ⇒ 零新公理）
--------------------------------------------------------------------------------

Ω3⁺-refl : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
           (c : Ω2Walk G x w1 w2) → Ω3Walk⁺ G x c c
Ω3⁺-refl = refl3+

Ω3⁺-symm : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
           {c c' : Ω2Walk G x w1 w2} → Ω3Walk⁺ G x c c' → Ω3Walk⁺ G x c' c
Ω3⁺-symm = symm3+

Ω3⁺-trans : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
            {c1 c2 c3 : Ω2Walk G x w1 w2}
          → Ω3Walk⁺ G x c1 c2 → Ω3Walk⁺ G x c2 c3 → Ω3Walk⁺ G x c1 c3
Ω3⁺-trans = trans3+
