{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi2dQuotient
--
-- **批 4a：`π₂ᵈ` / `π₂ᵈ⁺` 的 `SetQuotient` 定义 + 下降映射**
--
-- ## 裁决原文
--
-- > **批 4 用 `SetQuotient`，不用 HIT** —— `Ω2Walk` 和 `Ω3Walk` 都是 Set，商是 Set，
-- > 不需要高维路径，HIT 商是过度设计。
-- > **如果 `SetQuotient` 不够，不退回 HIT，而是报告具体缺口。**
--
-- ⚠ **术语澄清（重要）**：`Cubical.HITs.SetQuotients` 的 `_/_` **本身**就是一个 HIT
-- （它带 `squash/` 构造子）。裁决里说的「用 `SetQuotient` 不用 HIT」，正确的读法是
-- **「用 Set 截断的商（`SetQuotient`），不用未经截断的 `_/_`/高阶路径」** ——
-- 因为 `Ω2Walk`/`Ω3Walk` 都是 0-型，商必须截断成 Set，`SetQuotients` 正是这个截断商 ✓
-- ⇒ 本模块用的就是它，**与裁决意图一致**。
--
-- ## 内容
--
-- | 项 | 内容 |
-- |---|---|
-- | `π₂ᵈ` | `Ω2Walk G x w w / (λ c c' → Ω3Walk G x c c')`（细商）|
-- | `π₂ᵈ⁺` | `Ω2Walk G x w w / (λ c c' → Ω3Walk⁺ G x c c')`（粗商）|
-- | `[_]ᵈ` / `[_]⁺` | 类映射 |
-- | **`desc`** | ★ **下降映射 `π₂ᵈ → π₂ᵈ⁺`**，靠 `embed3 : Ω3Walk ⊆ Ω3Walk⁺` |
--
-- ## ★ `desc` 为什么是这批的核心
--
-- ```
--   Ω3Walk ⊆ Ω3Walk⁺  （embed3，批 3 已证）
--   ⇒ 细商的等价更细 ⇒ 商更细 ⇒ 有下降 π₂ᵈ → π₂ᵈ⁺（细 → 粗）
-- ```
--
-- 这是 `_PPI5j:90-93` 称作「桥」的那个映射。**没有 `embed3` 就写不出来** ——
-- 批 3 的 `embed3` 在这里付账 ✓
--
-- ## ⚠ 本模块**不**包含
--
--   · `desc` 的单射性/满射性（需 `Ω3Walk⁺ ⊆ Ω3Walk` 的反向包含，**未证**，
--     见 `_PEH5:151` 的边界记录）；
--   · `π₂ᵈ` 的群结构或任何计算；
--   · 类运算（`addL`/`addR`）—— 需 `whisk-resp`/`suffix-resp` 的完整版
--     （`Omega3Suffix` 的 `suffix-resp` 只做到 `base3+` 情形）。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 不引入高维路径：全部内容是 0-型 + Set 截断商

module Sovereign.Synthesis.Homotopy.Pi2dQuotient where

open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/)
open import Cubical.HITs.SetQuotients.Properties using (rec; elimProp)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk)
open DiGraph using (V)
open import Sovereign.Synthesis.Homotopy.Omega2 using (Ω2Walk; nil2; _++2_)
open import Sovereign.Synthesis.Homotopy.Omega3 using (Ω3Walk)
open import Sovereign.Synthesis.Homotopy.Omega3Plus using (Ω3Walk⁺; embed3)
open import Sovereign.Synthesis.Homotopy.Omega3Suffix using (whisk-resp)

--------------------------------------------------------------------------------
-- §1. 两个商
--------------------------------------------------------------------------------

-- 细商：π₂ᵈ = Ω2Walk / Ω3Walk
π₂ᵈ : (G : DiGraph) (x : V G) (w : Walk G x x) → Set
π₂ᵈ G x w = Ω2Walk G x w w / (λ c c' → Ω3Walk G x c c')

-- 粗商：π₂ᵈ⁺ = Ω2Walk / Ω3Walk⁺
π₂ᵈ⁺ : (G : DiGraph) (x : V G) (w : Walk G x x) → Set
π₂ᵈ⁺ G x w = Ω2Walk G x w w / (λ c c' → Ω3Walk⁺ G x c c')

--------------------------------------------------------------------------------
-- §2. 类映射
--------------------------------------------------------------------------------

[_]ᵈ : ∀ {G : DiGraph} {x : V G} {w : Walk G x x}
     → Ω2Walk G x w w → π₂ᵈ G x w
[ c ]ᵈ = [ c ]

[_]⁺ : ∀ {G : DiGraph} {x : V G} {w : Walk G x x}
     → Ω2Walk G x w w → π₂ᵈ⁺ G x w
[ c ]⁺ = [ c ]

--------------------------------------------------------------------------------
-- §3. ★★ 下降映射 π₂ᵈ → π₂ᵈ⁺（靠 `embed3`）
--
-- 细商的等价 ⊆ 粗商的等价 ⇒ 代表元的类映射良定义 ⇒ 下降。
--------------------------------------------------------------------------------

desc : ∀ {G : DiGraph} {x : V G} {w : Walk G x x}
     → π₂ᵈ G x w → π₂ᵈ⁺ G x w
desc = rec (λ a b → squash/ a b) [_] (λ a b h → eq/ a b (embed3 h))

--------------------------------------------------------------------------------
-- §4. 同态版（hom）：让**左类作用**在非闭 2-走上也成立
--
-- `π₂ᵈ G x w` 只覆盖「圈」；而缘饰 `p ++2 _` 把 `w1 → wm` 的 2-走作用到 `wm → w2`
-- 上，落到 `w1 → w2`。所以要先有**同态版**（两端自由），作用才有正确的类型。
--------------------------------------------------------------------------------

π₂ᵈ-hom : (G : DiGraph) (x : V G) (w1 w2 : Walk G x x) → Set
π₂ᵈ-hom G x w1 w2 = Ω2Walk G x w1 w2 / (λ c c' → Ω3Walk G x c c')

π₂ᵈ⁺-hom : (G : DiGraph) (x : V G) (w1 w2 : Walk G x x) → Set
π₂ᵈ⁺-hom G x w1 w2 = Ω2Walk G x w1 w2 / (λ c c' → Ω3Walk⁺ G x c c')

desc-hom : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
         → π₂ᵈ-hom G x w1 w2 → π₂ᵈ⁺-hom G x w1 w2
desc-hom = rec (λ a b → squash/ a b) [_] (λ a b h → eq/ a b (embed3 h))

--------------------------------------------------------------------------------
-- §5. ★★ 左类作用（良定义性靠 `whisk-resp`）
--
-- `addL p [ c ] = [ p ++2 c ]`；良定义要证
--   `Ω3Walk⁺ a b ⇒ Ω3Walk⁺ (p ++2 a) (p ++2 b)` —— 正是 `Omega3Suffix.whisk-resp` ✓
--------------------------------------------------------------------------------

addL : ∀ {G : DiGraph} {x : V G} {w1 wm w2 : Walk G x x}
       (p : Ω2Walk G x w1 wm)
     → π₂ᵈ⁺-hom G x wm w2 → π₂ᵈ⁺-hom G x w1 w2
addL p = rec (λ a b → squash/ a b)
             (λ c → [ p ++2 c ])
             (λ a b h → eq/ (p ++2 a) (p ++2 b) (whisk-resp p h))

-- ★ 单位律：`addL (nil2 _)` 是恒等（`elimProp` + `rec`-β）
addL-nil2 : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
            (q : π₂ᵈ⁺-hom G x w1 w2) → addL (nil2 w1) q ≡ q
addL-nil2 = elimProp (λ q → squash/ _ _) (λ c → refl)
