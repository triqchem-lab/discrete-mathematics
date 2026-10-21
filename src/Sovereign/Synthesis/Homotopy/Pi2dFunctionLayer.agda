{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi2dFunctionLayer
--
-- **`π₂ᵈ⁺` 的结构律：函数表示层**（人类 2026-10-21：「Cubical，我们前面的做法是函数表示层」）
--
-- ## 为什么用函数表示层
--
-- `Pi2dQuotient` 用了 `Cubical.HITs.SetQuotients._/_`（Set 截断商）。它**能编译**，
-- 但代价是：类层定律要靠 `elimProp` + `squash/`，且命题相等（propEq）与 Cubical 路径
-- 两个世界要做桥 —— `addL-inv` 在那条路上递了 12 次都没闭合。
--
-- **函数表示层**（库内既有做法，`Sovereign.Foundation.QuotientBasic`）：
--
-- ```
--   不取商。类 = 代表元 + 「目标运算尊重关系」（Respects）这一**谓词条件**。
--   ⇒ 「类层定律」退化为「代表元层的等式/关系」
--   ⇒ 不需要 elimProp、不需要 squash/、不需要任何 Cubical 基础设施 ✓
-- ```
--
-- ## 本模块的内容（**零 Cubical 导入**）
--
-- | 结构律 | 代表元层陈述 | 来源 |
-- |---|---|---|
-- | 结合 | `Ω3Walk⁺ ((a ++2 b) ++2 c) (a ++2 (b ++2 c))` | `≡→Ω3Walk⁺` + `++2-assoc` |
-- | 左单位 | `Ω3Walk⁺ (nil2 _ ++2 c) c` | **定义性**（`refl3+`）|
-- | 右单位 | `Ω3Walk⁺ (c ++2 nil2 _) c` | `≡→Ω3Walk⁺` + `++2-nilR` |
-- | **乘法同余** | `Ω3Walk⁺ a a' → Ω3Walk⁺ b b' → Ω3Walk⁺ (a ++2 b) (a' ++2 b')` | `suffix-resp` + `whisk-resp` |
-- | **左逆** | `Ω3Walk⁺ (c ++2 rev2 c) (nil2 _)` | `rev2-cancel`（`inv-left-Ω3`）|
-- | 右逆 | `Ω3Walk⁺ (rev2 c ++2 c) (nil2 _)` | ✅ **已证**：`Omega2ReverseInvol.inv-right-Ω3`（经 `rev2-invol`）|
--
-- **⇒ 在函数表示层，`π₂ᵈ⁺` 有：结合 + 双单位 + 同余 + 左逆 + **右逆** = 群。**
--   （右逆原先标「未证」，现已在 `Omega2ReverseInvol` 证出 —— 见 §6 的更正。）
--
-- ## 核心原则
--   · **0 Cubical 导入**（本模块只依赖 PropEq + `Omega2`/`Omega3*`/`Omega2Reverse`）
--   · 0 postulate / 0 hole
--   · 全部结构律**复用**既有件，不重证

module Sovereign.Synthesis.Homotopy.Pi2dFunctionLayer where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil)
open DiGraph using (V)
open import Sovereign.Synthesis.Homotopy.Omega2
  using (Ω2Walk; nil2; cons2; _++2_; ++2-nilR; ++2-assoc)
open import Sovereign.Synthesis.Homotopy.Omega3Plus
  using (Ω3Walk⁺; refl3+; trans3+)
open import Sovereign.Synthesis.Homotopy.Omega3Suffix
  using (whisk-resp; suffix-resp; ≡→Ω3Walk⁺)
open import Sovereign.Synthesis.Homotopy.Omega2Reverse
  using (rev2; rev2-cancel; suffix-cancel)

--------------------------------------------------------------------------------
-- §1. 左单位：**定义性**（`nil2 _ ++2 c = c` 是 `_++2_` 的定义）
--------------------------------------------------------------------------------

unit-left : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
            (c : Ω2Walk G x w1 w2)
          → Ω3Walk⁺ G x (nil2 w1 ++2 c) c
unit-left c = refl3+ c

--------------------------------------------------------------------------------
-- §2. 右单位：`c ++2 nil2 _ ≡ c` 是**命题**等式 ⇒ 经桥 `≡→Ω3Walk⁺` 入关系
--------------------------------------------------------------------------------

unit-right : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
             (c : Ω2Walk G x w1 w2)
           → Ω3Walk⁺ G x (c ++2 nil2 w2) c
unit-right c = ≡→Ω3Walk⁺ (++2-nilR c)

--------------------------------------------------------------------------------
-- §3. 结合律：同样是命题等式 ⇒ 经桥入关系
--------------------------------------------------------------------------------

assoc-Ω3 : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 w4 : Walk G x x}
           (a : Ω2Walk G x w1 w2) (b : Ω2Walk G x w2 w3) (c : Ω2Walk G x w3 w4)
         → Ω3Walk⁺ G x ((a ++2 b) ++2 c) (a ++2 (b ++2 c))
assoc-Ω3 a b c = ≡→Ω3Walk⁺ (++2-assoc a b c)

--------------------------------------------------------------------------------
-- §4. ★★ 乘法同余（商面良定义性在函数表示层的**全部内容**）
--
-- 左因子用**右缘饰**、右因子用**左缘饰** —— 两个缘饰稳定性刚好覆盖两侧。
--------------------------------------------------------------------------------

cong₂-Ω3 : ∀ {G : DiGraph} {x : V G} {w1 wm w2 : Walk G x x}
           {a a' : Ω2Walk G x w1 wm} {b b' : Ω2Walk G x wm w2}
         → Ω3Walk⁺ G x a a' → Ω3Walk⁺ G x b b'
         → Ω3Walk⁺ G x (a ++2 b) (a' ++2 b')
cong₂-Ω3 h1 h2 =
  trans3+ (suffix-resp _ h1) (whisk-resp _ h2)

--------------------------------------------------------------------------------
-- §5. ★★ 左逆（`rev2-cancel` 的重述；名字避开 `DCCayleyGraph.inv-left`）：`c ·₂ c⁻¹ ⁓ 单位`
--------------------------------------------------------------------------------

inv-left-Ω3 : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
           (c : Ω2Walk G x w1 w2)
         → Ω3Walk⁺ G x (c ++2 rev2 c) (nil2 w1)
inv-left-Ω3 = rev2-cancel

-- 带右端上下文的形式（`addL-inv` 在类层的等价物，已顶层证毕）
inv-left-ctx : ∀ {G : DiGraph} {x : V G} {w : Walk G x x}
               (c c' : Ω2Walk G x w w)
             → Ω3Walk⁺ G x (c ++2 (rev2 c ++2 c')) c'
inv-left-ctx = suffix-cancel

--------------------------------------------------------------------------------
-- §6. ✅ 右逆：**已在 `Omega2ReverseInvol` 证出**（本节原标「⬜ 未证」已过期）
--
-- 原判断：「需要 `rev2 (rev2 c) ≡ c`，或第二次 `++2-assoc` 运输；本模块暂不做，如实标注」。
-- 事实（跨模块核对）：`Omega2ReverseInvol` 已完成两条 ——
--   · `rev2-invol : rev2 (rev2 c) ≡ c`（对合，那里 §2）
--   · `inv-right-Ω3 c : Ω3Walk⁺ G x (rev2 c ++2 c) (nil2 w2)`（右逆本体，那里 §3）
-- ⇒ 本模块与该模块是**同一批的两半**：本模块给左逆（`inv-left-Ω3` = `rev2-cancel`），
--   右逆在 `Omega2ReverseInvol`。
--
-- ⚠ 不能在此**再导出**：`Omega2ReverseInvol` 反向 import 了本模块 ⇒ 会触发
--   `CyclicModuleDependency`（实测）。所以这里只留**指针**，代码各就各位。
--------------------------------------------------------------------------------
