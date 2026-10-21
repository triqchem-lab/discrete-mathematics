{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Omega3Suffix
--
-- **`Ω3Walk⁺` 的缘饰稳定性** —— 商 `π₂ᵈ` 良定义性的实质前提（**不需要商本身**）
--
-- ## 为什么要做这个（批 4 的前置，可自决部分）
--
-- 要让 `π₂ᵈ⁺` 的**类运算**良定义，需要关系对缘饰稳定：
--
-- ```
--   whisk-resp  : Ω3Walk⁺ c c' → Ω3Walk⁺ (p ++2 c) (p ++2 c')      （左缘饰）
--   suffix-resp : Ω3Walk⁺ c c' → Ω3Walk⁺ (c ++2 e) (c' ++2 e)      （右缘饰）
-- ```
--
-- **这两条是纯关系层的命题，不需要 `_/_`** ⇒ 在商型选择待裁期间即可推进。
--
-- ## 本模块交付
--
-- | 引理 | 内容 | 状态 |
-- |---|---|---|
-- | `Resp2` | 尊重性条件（商 `rec` 的前提形）—— 定义 | ✅ |
-- | **`whisk-resp`** | 左缘饰稳定，**四情形全证**（`gen3+` 情形恰由 `whisk3` 构造子给出）| ✅ |
-- | **`suffix-base3`** | ★ **右缘饰的 `base3+` 情形**，**恰好由 `bub3` 给出** | ✅ |
-- | `suffix-resp`（全）| `whisk3`/`bub3` 两情形需 `++2-assoc` 运输 | ⬜ 待做 |
--
-- ## ★ `suffix-base3` 的意义：**这就是 `bub3` 存在的理由**
--
-- 原生成集只有 `fill-tri`：`cons2 s (cons2 (invAStep s) (nil2 w)) ⁓ nil2 w`
-- —— 它只在**右端接 `nil2`** 时成立。
--
-- 右缘饰要求同一 3-步在**右端接任意 `c₂`** 时仍成立：
-- `cons2 s (cons2 (invAStep s) c₂) ⁓ c₂`
-- —— 这条**不能**由 `fill-tri` 推出（右端不是 `nil2`）。
-- **`bub3` 正是补这一格**：
--
-- ```agda
-- suffix-base3 s c₂ = gen3+ (bub3 (nil2 w) s c₂)
-- ```
--
-- 代入 `c₂ := nil2 w` 就**退化为 `fill-tri`** ⇒ `bub3` 是把 `fill-tri` 从
-- 「`nil2` 右端」推广到「任意右端」的最小扩展，**不是加新公理** ✓
--
-- ## ⚠ 本模块**不**包含
--
--   · 完整的 `suffix-resp`（`whisk3`/`bub3` 两情形要 `++2-assoc` 的命题运输）；
--   · 商 `π₂ᵈ` / `π₂ᵈ⁺` —— 提升批 4，**需裁** `src/Homotopy/` 是否允许 cubical `_/_`；
--   · 任何**计算**（`π₂ᵈ` 的群结构、非平凡实例）。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `Omega3Plus` 的 `Ω3Walk⁺` / `bub3` / 三律（不重证）

module Sovereign.Synthesis.Homotopy.Omega3Suffix where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; AStep)
open DiGraph using (V)
open import Sovereign.Synthesis.Homotopy.Omega2
  using (Ω2Walk; nil2; cons2; _++2_; ++2-assoc)
open import Sovereign.Synthesis.Homotopy.Omega3 using (invAStep; fill-tri)
open import Sovereign.Synthesis.Homotopy.Omega3Plus
  using (Ω3Step⁺; Ω3Walk⁺; refl3+; symm3+; trans3+; gen3+; base3+; whisk3; bub3; bub; embed3)

--------------------------------------------------------------------------------
-- §1. 尊重性条件（商 `rec` 的前提形 —— 定义，不是定理）
--------------------------------------------------------------------------------

Resp2 : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
      → (B : Set) → (Ω2Walk G x w1 w2 → B) → Set
Resp2 {G} {x} {w1} {w2} B h =
  (c c' : Ω2Walk G x w1 w2) → Ω3Walk⁺ G x c c' → h c ≡ h c'

--------------------------------------------------------------------------------
-- §2. ★ 左缘饰稳定（四情形全证）
--
-- `gen3+` 情形恰由 `whisk3` 构造子给出 ⇒ **定义性**，无需运输 ✓
--------------------------------------------------------------------------------

whisk-resp : ∀ {G : DiGraph} {x : V G} {w1 wm w2 : Walk G x x}
             (p : Ω2Walk G x w1 wm)
             {c c' : Ω2Walk G x wm w2}
           → Ω3Walk⁺ G x c c' → Ω3Walk⁺ G x (p ++2 c) (p ++2 c')
whisk-resp p (refl3+ c)      = refl3+ (p ++2 c)
whisk-resp p (symm3+ h)      = symm3+ (whisk-resp p h)
whisk-resp p (trans3+ h1 h2) = trans3+ (whisk-resp p h1) (whisk-resp p h2)
whisk-resp p (gen3+ st)      = gen3+ (whisk3 p st)

--------------------------------------------------------------------------------
-- §3. ★★ 右缘饰的 `base3+` 情形 —— **恰好由 `bub3` 给出**
--------------------------------------------------------------------------------

suffix-base3 : ∀ {G : DiGraph} {x : V G} {w w' w2 : Walk G x x}
               (s : AStep G w w') (c₂ : Ω2Walk G x w w2)
             → Ω3Walk⁺ G x (cons2 s (cons2 (invAStep s) c₂)) c₂
suffix-base3 s c₂ = gen3+ (bub3 (nil2 _) s c₂)

--------------------------------------------------------------------------------
-- §4. 索引运输（`++2-assoc` 的命题等式要运输 `Ω3Step⁺` / `Ω3Walk⁺`）
--------------------------------------------------------------------------------

subst₂-Ω3Step⁺ : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
                  {a a' b b' : Ω2Walk G x w1 w2}
               → a ≡ a' → b ≡ b' → Ω3Step⁺ G x a b → Ω3Step⁺ G x a' b'
subst₂-Ω3Step⁺ refl refl z = z

subst₂-Ω3Walk⁺ : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
                  {a a' b b' : Ω2Walk G x w1 w2}
               → a ≡ a' → b ≡ b' → Ω3Walk⁺ G x a b → Ω3Walk⁺ G x a' b'
subst₂-Ω3Walk⁺ refl refl z = z

--------------------------------------------------------------------------------
-- §5. ★★ 步层右缘饰：`Ω3Step⁺` 在 `_++2 e` 下稳定
--
-- 三情形：
--   · `base3+` —— **定义性**由 `bub3` 给出（`(nil2 ++2 bub s) ++2 e = bub s ++2 e` ✓）
--   · `whisk3` —— 归纳 + 两次 `++2-assoc` 运输
--   · `bub3`   —— 归纳体 `bub3 c₁ s (c₂ ++2 e)` + 两次 `++2-assoc` 运输
--------------------------------------------------------------------------------

suffix-step : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 : Walk G x x}
              {c c' : Ω2Walk G x w1 w2} (e : Ω2Walk G x w2 w3)
            → Ω3Step⁺ G x c c' → Ω3Step⁺ G x (c ++2 e) (c' ++2 e)

suffix-step e (base3+ (fill-tri s)) = bub3 (nil2 _) s e

suffix-step e (whisk3 c₁ {c} {c'} st) =
  subst₂-Ω3Step⁺ (sym (++2-assoc c₁ c e)) (sym (++2-assoc c₁ c' e))
                 (whisk3 c₁ (suffix-step e st))

suffix-step e (bub3 c₁ {wm'} s c₂) =
  subst₂-Ω3Step⁺ (sym (++2-assoc (c₁ ++2 bub s) c₂ e))
                 (sym (++2-assoc c₁ c₂ e))
                 (bub3 c₁ s (c₂ ++2 e))

--------------------------------------------------------------------------------
-- §6. ★★ 闭包层右缘饰：`Ω3Walk⁺` 在 `_++2 e` 下稳定（四情形）
--
-- 与 `whisk-resp` 完全同构 —— `gen3+` 情形由 §5 的 `suffix-step` 给出。
--------------------------------------------------------------------------------

suffix-resp : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 : Walk G x x}
              {c c' : Ω2Walk G x w1 w2} (e : Ω2Walk G x w2 w3)
            → Ω3Walk⁺ G x c c' → Ω3Walk⁺ G x (c ++2 e) (c' ++2 e)
suffix-resp e (refl3+ c)      = refl3+ (c ++2 e)
suffix-resp e (symm3+ h)      = symm3+ (suffix-resp e h)
suffix-resp e (trans3+ h1 h2) = trans3+ (suffix-resp e h1) (suffix-resp e h2)
suffix-resp e (gen3+ st)      = gen3+ (suffix-step e st)

--------------------------------------------------------------------------------
-- §7. ★★ 桥：命题相等 ⊆ `Ω3Walk⁺`
--
-- `a ≡ b`（命题相等，2-走的**同一性**）⇒ `Ω3Walk⁺ a b`。按 `refl` 归纳即可 ——
-- 因为 `refl` 情形退化为 `refl3+ a` ✓
--
-- **这条桥的用途**：`++2` 的代数律（`++2-nilR`、`++2-assoc`）是**命题**等式，
-- 而商的类相等是 **Cubical 路径**。有了这条桥，`eq/` 可以直接吃命题等式
-- ⇒ **不需要 propEq→path 的桥**，也不需要改 `_++2_` 的定义形状。
--
-- 数学上无风险：`Ω2Walk` 是语法对象，命题相等就是「同一个 2-走」，
-- 让关系包含它只是 `refl3+` 沿等式运输 ✓
--------------------------------------------------------------------------------

≡→Ω3Walk⁺ : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
            {a b : Ω2Walk G x w1 w2} → a ≡ b → Ω3Walk⁺ G x a b
≡→Ω3Walk⁺ refl = refl3+ _
