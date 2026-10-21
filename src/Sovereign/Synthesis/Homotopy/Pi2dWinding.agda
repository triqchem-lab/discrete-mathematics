{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi2dWinding
--
-- **`π₂ᵈ⁺` 的位移不变量（`ℤ` 值）** —— 比奇偶**细得多**的分裂器
--
-- ## 为什么需要更细的不变量
--
-- `Pi2dParity.par2`（步数奇偶）只是**必要条件**：它把类分到 2 格，
-- 但**同奇偶不一定同类**，所以拿不到类数上界，也拿不到「多于两类」。
--
-- 本模块给一个 `ℤ` 值不变量：
--
-- ```
--   wstep : AStep G w w' → ℤ     slide ↦ +1，expand ↦ −1
--   wind  : Ω2Walk G x w1 w2 → ℤ  逐步求和
-- ```
--
-- ## 为什么它是 `Ω3Walk⁺` 不变量（关键：`bub` 的位移恰为 0）
--
-- | 生成元 | 位移 |
-- |---|---|
-- | `bub s = s ∘ s⁻¹` | `wstep s + wstep (invAStep s) = (+1) + (−1) = 0` ✓ |
-- | `whisk3` | 两侧同加 `wind c₁` ✓ |
-- | `bub3` | 消掉一个 `bub s`（位移 0）⇒ 不变 ✓ |
--
-- ⇒ **`wind-Walk⁺ : Ω3Walk⁺ c c' → wind c ≡ wind c'`**
--
-- ## 与奇偶的关系
--
-- `wind` **比** `par2` **细**：`wind` 相同 ⇒ 奇偶相同（差是偶数），反之不然。
-- 例：`cons2 s (nil2)`（wind = +1）与 `cons2 s (cons2 s (nil2))`（wind = +2）
-- 奇偶**相同**但 wind **不同** ⇒ **不同类** ⇒ **至少 3 类**。
-- 一般地：`n` 次迭代给出 `n+1` 个互不相同的类 ⇒ **无穷多类**（见 §5 的路线）。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；**零 Cubical**
--   · 逐案证明（`ASTep` 只有两个构造子 ⇒ 所有关键小律都是 2-case）

module Sovereign.Synthesis.Homotopy.Pi2dWinding where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_)
open import Data.Integer.Properties using (+-identityʳ; +-identityˡ; +-assoc)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; AStep; slide; expand)
open DiGraph using (V)
open import Sovereign.Synthesis.Homotopy.Omega2
  using (Ω2Walk; nil2; cons2; _++2_)
open import Sovereign.Synthesis.Homotopy.Omega3
  using (invAStep; fill-tri)
open import Sovereign.Synthesis.Homotopy.Omega3Plus
  using (Ω3Step⁺; Ω3Walk⁺; refl3+; symm3+; trans3+; gen3+; base3+; whisk3; bub3; bub)

--------------------------------------------------------------------------------
-- §1. 单步位移：`slide` 记 +1，`expand` 记 −1
--------------------------------------------------------------------------------

wstep : ∀ {G : DiGraph} {u v : V G} {p q : Walk G u v} → AStep G p q → ℤ
wstep (slide  _ _ _ _ _) = + 1
wstep (expand _ _ _ _ _) = -[1+ 0 ]

-- ★ 关键：一步与它的逆，位移相加为 0
wstep-cancel : ∀ {G : DiGraph} {u v : V G} {p q : Walk G u v} (s : AStep G p q)
             → wstep s + wstep (invAStep s) ≡ + 0
wstep-cancel (slide  _ _ _ _ _) = refl
wstep-cancel (expand _ _ _ _ _) = refl

--------------------------------------------------------------------------------
-- §2. 位移：逐步求和
--------------------------------------------------------------------------------

wind : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
     → Ω2Walk G x w1 w2 → ℤ
wind (nil2 _)    = + 0
wind (cons2 s c) = wstep s + wind c

wind-++2 : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 : Walk G x x}
           (a : Ω2Walk G x w1 w2) (b : Ω2Walk G x w2 w3)
         → wind (a ++2 b) ≡ wind a + wind b
wind-++2 (nil2 _)    b = sym (+-identityˡ (wind b))
wind-++2 (cons2 s a) b =
  trans (cong (λ z → wstep s + z) (wind-++2 a b))
        (sym (+-assoc (wstep s) (wind a) (wind b)))

-- ★★ 气泡的位移恰为 0
wind-bub : ∀ {G : DiGraph} {x : V G} {w w' : Walk G x x}
           (s : AStep G w w') → wind (bub s) ≡ + 0
wind-bub s =
  trans (cong (λ z → wstep s + z) (+-identityʳ (wstep (invAStep s))))
        (wstep-cancel s)

--------------------------------------------------------------------------------
-- §3. ★★ 三步生成元保持位移（三情形）
--------------------------------------------------------------------------------

wind-step⁺ : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
             {c c' : Ω2Walk G x w1 w2}
           → Ω3Step⁺ G x c c' → wind c ≡ wind c'
-- ① `fill-tri`：`bub s ⁓ nil2`，两边位移都是 0
wind-step⁺ (base3+ (fill-tri s)) = wind-bub s

-- ② `whisk3`：两侧同加 `wind c₁`
wind-step⁺ (whisk3 c₁ {c = d} {c' = d'} st) =
  trans (wind-++2 c₁ d)
        (trans (cong (λ z → wind c₁ + z) (wind-step⁺ st))
               (sym (wind-++2 c₁ d')))

-- ③ `bub3`：消掉位移为 0 的气泡
wind-step⁺ (bub3 c₁ s c₂) =
  trans (wind-++2 (c₁ ++2 bub s) c₂)
        (trans (cong (λ z → z + wind c₂) (wind-++2 c₁ (bub s)))
        (trans (cong (λ z → (wind c₁ + z) + wind c₂) (wind-bub s))
        (trans (cong (λ z → z + wind c₂) (+-identityʳ (wind c₁)))
               (sym (wind-++2 c₁ c₂)))))

--------------------------------------------------------------------------------
-- §4. ★★ 闭包层不变性
--------------------------------------------------------------------------------

wind-Walk⁺ : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
             {c c' : Ω2Walk G x w1 w2}
           → Ω3Walk⁺ G x c c' → wind c ≡ wind c'
wind-Walk⁺ (refl3+ _)      = refl
wind-Walk⁺ (symm3+ h)      = sym (wind-Walk⁺ h)
wind-Walk⁺ (trans3+ h1 h2) = trans (wind-Walk⁺ h1) (wind-Walk⁺ h2)
wind-Walk⁺ (gen3+ st)      = wind-step⁺ st

--------------------------------------------------------------------------------
-- §5. ★★★ 无穷多类：自步的迭代给出互不相同的类
--
-- `iter s n` = 自步 `s` 叠 `n` 层（`nit` 的位移恰为 `+ n`）。
-- ⇒ 不同的 `n` 给出不同的 `wind` ⇒ 由 `wind-Walk⁺` 的逆否 ⇒ **不同类**。
--
-- **⇒ 在有自步的基点上，`π₂ᵈ⁺` 有无穷多个元素**（不是只有「≥2」）。
--------------------------------------------------------------------------------
-- `+_ : ℕ → ℤ` 单射（构造子单射，一行）
+injective : {m n : ℕ} → + m ≡ + n → m ≡ n
+injective refl = refl

-- ⚠ 关键修正：`wstep s` 可以是 −1（`expand` 步），所以「叠 n 层 ⇒ 位移 +n」
--   只在 `s` 被定向为 `+1` 时成立 ⇒ **把取向作为假设传进来**。
iterUp : ∀ {G : DiGraph} {x : V G} {w : Walk G x x}
       → (s : AStep G w w) → wstep s ≡ + 1 → ℕ → Ω2Walk G x w w
iterUp s _ zero    = nil2 _
iterUp s h (suc n) = cons2 s (iterUp s h n)

wind-iterUp : ∀ {G : DiGraph} {x : V G} {w : Walk G x x}
              (s : AStep G w w) (h : wstep s ≡ + 1) (n : ℕ)
            → wind (iterUp s h n) ≡ + n
wind-iterUp s h zero    = refl
wind-iterUp s h (suc n) =
  trans (cong (λ z → z + wind (iterUp s h n)) h)
        (trans (cong (λ z → + 1 + z) (wind-iterUp s h n)) refl)

-- ★★★ 不同层数 ⇒ 不同类 ⇒ **无穷多类**（`+1` 取向下）
no-collapse : ∀ {G : DiGraph} {x : V G} {w : Walk G x x}
              (s : AStep G w w) (h : wstep s ≡ + 1) (m n : ℕ)
            → m ≢ n → ¬ (Ω3Walk⁺ G x (iterUp s h m) (iterUp s h n))
no-collapse s h m n neq k =
  neq (+injective (trans (sym (wind-iterUp s h m))
                         (trans (wind-Walk⁺ k) (wind-iterUp s h n))))
