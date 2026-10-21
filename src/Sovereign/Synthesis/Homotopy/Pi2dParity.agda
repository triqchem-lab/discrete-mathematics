{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi2dParity
--
-- **`π₂ᵈ⁺` 的奇偶不变量**：奇偶是**类函数**（良定义）；有自步时**至少两类**
--
-- ## 数学直觉
--
-- 三类 3-步生成元对**步数**的影响：
--
-- | 生成元 | 源 → 靶 步数 | 差 |
-- |---|---|---|
-- | `fill-tri` | 2 → 0 | −2 |
-- | `bub3` | `c₁ ++ 2 + c₂` → `c₁ + c₂` | −2 |
-- | `whisk3` | `c₁ ++ #c` → `c₁ ++ #c'` | 同 IH |
--
-- **都是偶数变化** ⇒ **步数奇偶性是 `Ω3Walk⁺` 的不变量** ✓
--
-- ## 结论（**已修正**：初版误称「至多两类」，那是错的）
--
-- 1. **奇偶是良定义的类函数**：`Ω3Walk⁺ c c' → par2 c ≡ par2 c'`
--    ⇒ 得到「类 ↦ 奇偶」这个**分裂器**（separator）。
--    ⚠ **良定义 ≠ 单射**：到二元集的函数对类数**没有上界**。
--    要上界需要「同奇偶 ⇒ 同类」（奇偶的**完备性**），本模块**没有**也不行。
-- 2. **至少两类**（非平凡实例）：若基点上存在**自步** `s : AStep G w w`，
--    则 `nil2 w` 与 `cons2 s (nil2 w)` 奇偶不同 ⇒ **不同类**
--    ⇒ `π₂ᵈ⁺` 在该基点**至少有 2 个元素**。
--
-- **⇒ 本模块能下的结论只有：`π₂ᵈ⁺` 非平凡 + 奇偶是分裂器。
--    类数的上界需要别的（更细的）不变量 —— 未做。**
--
-- ## 关于 `Ω2Walk` 索引的一个事实（本模块顺带澄清）
--
-- `ASTep G p q` 的两个 walk 参数 `p q : Walk G x x` **端点相同**
-- ⇒ `cons2` 不改变端点 ⇒ `Ω2Walk G x w1 w2` **只在 `w1`、`w2` 相等时可居留**。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；**零 Cubical**
--   · 不变量用 `Bool`（`xor`），不做 `ℕ` mod 运算

module Sovereign.Synthesis.Homotopy.Pi2dParity where

open import Data.Bool using (Bool; true; false; not)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; AStep)
open DiGraph using (V)
open import Sovereign.Synthesis.Homotopy.Omega2
  using (Ω2Walk; nil2; cons2; _++2_)
open import Sovereign.Synthesis.Homotopy.Omega3
  using (invAStep; fill-tri)
open import Sovereign.Synthesis.Homotopy.Omega3Plus
  using (Ω3Step⁺; Ω3Walk⁺; refl3+; symm3+; trans3+; gen3+; base3+; whisk3; bub3; bub)

--------------------------------------------------------------------------------
-- §1. `Bool` 上的异或与两条小律
--------------------------------------------------------------------------------

xorB : Bool → Bool → Bool
xorB false b = b
xorB true  b = not b

not-not : ∀ (b : Bool) → not (not b) ≡ b
not-not false = refl
not-not true  = refl

xorB-flip : ∀ (a b : Bool) → xorB (not a) b ≡ not (xorB a b)
xorB-flip false b = refl
xorB-flip true  b = sym (not-not b)

xorB-id : ∀ (a : Bool) → xorB a false ≡ a
xorB-id false = refl
xorB-id true  = refl

--------------------------------------------------------------------------------
-- §2. 2-走的奇偶：每加一步就翻转
--------------------------------------------------------------------------------

par2 : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
     → Ω2Walk G x w1 w2 → Bool
par2 (nil2 _)    = false
par2 (cons2 _ c) = not (par2 c)

par2-++2 : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 : Walk G x x}
           (a : Ω2Walk G x w1 w2) (b : Ω2Walk G x w2 w3)
         → par2 (a ++2 b) ≡ xorB (par2 a) (par2 b)
par2-++2 (nil2 _)    b = refl
par2-++2 (cons2 _ a) b =
  trans (cong not (par2-++2 a b)) (sym (xorB-flip (par2 a) (par2 b)))

-- `bub s` 的奇偶是偶数（两步）
par2-bub : ∀ {G : DiGraph} {x : V G} {w w' : Walk G x x}
           (s : AStep G w w') → par2 (bub s) ≡ false
par2-bub s = refl

--------------------------------------------------------------------------------
-- §3. ★★ 三步生成元保持奇偶（三情形）
--------------------------------------------------------------------------------

par2-step⁺ : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
             {c c' : Ω2Walk G x w1 w2}
           → Ω3Step⁺ G x c c' → par2 c ≡ par2 c'
-- ① `fill-tri`：`s ∘ s⁻¹` 是**两步** ⇒ 偶 ⇔ 偶（**必须解构到 `fill-tri`** 才能归约）
par2-step⁺ (base3+ (fill-tri s)) = refl

-- ② `whisk3`：前缀不影响奇偶差
par2-step⁺ (whisk3 c₁ {c = d} {c' = d'} st) =
  trans (par2-++2 c₁ d)
        (trans (cong (xorB (par2 c₁)) (par2-step⁺ st))
               (sym (par2-++2 c₁ d')))

-- ③ `bub3`：去掉一个**偶**气泡 ⇒ 奇偶不变
--   （`c`/`c'` 由签名绑定；`bub3` 的索引在此处**定义性**归约为目标两侧）
par2-step⁺ (bub3 c₁ s c₂) =
  trans (par2-++2 (c₁ ++2 bub s) c₂)
        (trans (cong (λ z → xorB z (par2 c₂)) (par2-++2 c₁ (bub s)))
        (trans (cong (λ z → xorB (xorB (par2 c₁) z) (par2 c₂)) (par2-bub s))
        (trans (cong (λ z → xorB z (par2 c₂)) (xorB-id (par2 c₁)))
               (sym (par2-++2 c₁ c₂)))))

--------------------------------------------------------------------------------
-- §4. ★★ 闭包层不变性 ⇒ 奇偶是**良定义的类函数**（分裂器，非上界）
--------------------------------------------------------------------------------

par2-Walk⁺ : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
             {c c' : Ω2Walk G x w1 w2}
           → Ω3Walk⁺ G x c c' → par2 c ≡ par2 c'
par2-Walk⁺ (refl3+ _)         = refl
par2-Walk⁺ (symm3+ h)         = sym (par2-Walk⁺ h)
par2-Walk⁺ (trans3+ h1 h2)    = trans (par2-Walk⁺ h1) (par2-Walk⁺ h2)
par2-Walk⁺ (gen3+ st)         = par2-step⁺ st

--------------------------------------------------------------------------------
-- §5. ★★ 非平凡实例：有自步时**至少**两类
--
-- `nil2 w` 的奇偶是 `false`；`cons2 s (nil2 w)` 的是 `true`
-- ⇒ 若二者同类，由不变性得 `false ≡ true`，矛盾 ✓
--------------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

two-classes : ∀ {G : DiGraph} {x : V G} {w : Walk G x x}
              (s : AStep G w w)
            → ¬ (Ω3Walk⁺ G x (nil2 w) (cons2 s (nil2 w)))
two-classes s h = false≢true (par2-Walk⁺ h)
