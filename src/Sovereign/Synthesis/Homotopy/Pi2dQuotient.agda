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
-- ⚠ 用 `import ... as`（不是 `open import`）：只要限定名 PE.x，不把 PE._≡_ 带进无前缀作用域
import Relation.Binary.PropositionalEquality as PE
open import Sovereign.Synthesis.Homotopy.Omega2
  using (Ω2Walk; nil2; _++2_; ++2-nilR; ++2-assoc)
open import Sovereign.Synthesis.Homotopy.Omega3 using (Ω3Walk)
open import Sovereign.Synthesis.Homotopy.Omega3Plus using (Ω3Walk⁺; embed3)
open import Sovereign.Synthesis.Homotopy.Omega3Suffix
  using (whisk-resp; suffix-resp; ≡→Ω3Walk⁺)

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

--------------------------------------------------------------------------------
-- §6. ★★ 右类作用（良定义性靠 `suffix-resp`）
--
-- `addR e [ c ] = [ c ++2 e ]`；良定义要证
--   `Ω3Walk⁺ a b ⇒ Ω3Walk⁺ (a ++2 e) (b ++2 e)` —— 正是 `Omega3Suffix.suffix-resp` ✓
--
-- 与 `addL` 对偶：**左作用靠左缘饰、右作用靠右缘饰**。
--------------------------------------------------------------------------------

addR : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 : Walk G x x}
       (e : Ω2Walk G x w2 w3)
     → π₂ᵈ⁺-hom G x w1 w2 → π₂ᵈ⁺-hom G x w1 w3
addR e = rec (λ a b → squash/ a b)
             (λ c → [ c ++2 e ])
             (λ a b h → eq/ (a ++2 e) (b ++2 e) (suffix-resp e h))

--------------------------------------------------------------------------------
-- §7. ⬜ 未做（如实标注）
--
-- `addR` 的**单位律** `addR (nil2 _) q ≡ q` **未证**，原因是一个真实的**跨世界摩擦**：
--   `c ++2 nil2 _ ≡ c` 是 **命题相等**（`Omega2.++2-nilR`，`propEq`），
--   而商 `π₂ᵈ⁺` 的类相等是 **Cubical 路径**。
--   要让 `[ c ++2 nil2 _ ] ≡ [ c ]` 成立，需要把 propEq 转成 path ——
--   库内没有这条桥（`addL-nil2` 能证是因为 `nil2 _ ++2 c = c` 在 `_++2_` 的**定义**里就成立，
--   是**定义相等**，两边直接是同一个项 ⇒ `refl` ✓）。
--
-- ⇒ 这是「`_++2_` 的右单位律是命题的而非定义的」的后果，
--   要补则需要 `propEq → Cubical path` 的桥（或改 `_++2_` 的定义形状）。
--   **不是 K 墙，不是 `SetQuotient` 的缺口**，是两种相等世界的接口缺失。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §8. ★★ 结构律（上一轮记的「propEq vs Cubical」缺口，由 `≡→Ω3Walk⁺` 桥解掉）
--------------------------------------------------------------------------------

-- ★ 右作用的单位律（上一轮标为未证，现存证）
addR-nil2 : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
            (q : π₂ᵈ⁺-hom G x w1 w2) → addR (nil2 w2) q ≡ q
addR-nil2 = elimProp (λ q → squash/ _ _)
  (λ c → eq/ (c ++2 nil2 _) c (≡→Ω3Walk⁺ (++2-nilR c)))

-- ★ 左作用的结合律 ⇒ 左作用是**幺半群作用**
addL-assoc : ∀ {G : DiGraph} {x : V G} {w1 wm wm' w2 : Walk G x x}
             (p : Ω2Walk G x w1 wm) (q : Ω2Walk G x wm wm')
             (r : π₂ᵈ⁺-hom G x wm' w2)
           → addL p (addL q r) ≡ addL (p ++2 q) r
addL-assoc p q = elimProp (λ r → squash/ _ _)
  (λ c → eq/ (p ++2 (q ++2 c)) ((p ++2 q) ++2 c)
             (≡→Ω3Walk⁺ (PE.sym (++2-assoc p q c))))

-- ★ 右作用的结合律（顺序相反：先 `e2` 后 `e1`）
addR-assoc : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 w4 : Walk G x x}
             (e1 : Ω2Walk G x w3 w4) (e2 : Ω2Walk G x w2 w3)
             (q : π₂ᵈ⁺-hom G x w1 w2)
           → addR e1 (addR e2 q) ≡ addR (e2 ++2 e1) q
addR-assoc e1 e2 = elimProp (λ q → squash/ _ _)
  (λ c → eq/ ((c ++2 e2) ++2 e1) (c ++2 (e2 ++2 e1))
             (≡→Ω3Walk⁺ (++2-assoc c e2 e1)))
