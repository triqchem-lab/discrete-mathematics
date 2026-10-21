{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Pi2dWindingRev
--
-- **相干律**：`wind` 把群逆 `rev2` 看成「取负」 —— `π₂ᵈ⁺ →+ ℤ` 是**群同态**
--
-- ## 已有的一半与要补的另一半
--
-- `Pi2dWinding` 已有：
-- ```
--   wind-++2   : wind (a ++2 b) ≡ wind a + wind b     （乘 → 加，幺半群同态）
--   wind-Walk⁺ : Ω3Walk⁺ c c' → wind c ≡ wind c'      （良定义 ⇒ 下降到类）
-- ```
-- ⇒ `wind` 已经是**幺半群同态** `π₂ᵈ⁺ → ℤ`。
--
-- 但群同态还差一条：**逆要送到负元**。本模块补：
-- ```
--   wind-rev2 : wind (rev2 c) + wind c ≡ + 0
-- ```
-- （写成「和为零」而**不用一元负号**，避免 `Data.Integer` 的 `-_`/`+_` 语法纠缠。）
--
-- ## 证明要点
--
-- 归纳。`cons2 s c` 情形要两条小律的配合：
-- - `wstep-inv-sum : wstep (invAStep s) + wstep s ≡ + 0`（`ASTep` 两构造子 ⇒ 2-case refl）
-- - `+` 的结合律/单位律（`Data.Integer.Properties` 现成）
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `Pi2dWinding` 的 `wind` / `wind-++2` 与 `Omega2Reverse` 的 `rev2`

module Sovereign.Synthesis.Homotopy.Pi2dWindingRev where

open import Data.Integer using (ℤ; +_; _+_)
open import Data.Integer.Properties using (+-assoc; +-identityʳ; +-identityˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; AStep; slide; expand)
open DiGraph using (V)
open import Sovereign.Synthesis.Homotopy.Omega2
  using (Ω2Walk; nil2; cons2; _++2_)
open import Sovereign.Synthesis.Homotopy.Omega3
  using (invAStep)
open import Sovereign.Synthesis.Homotopy.Omega2Reverse
  using (rev2)
open import Sovereign.Synthesis.Homotopy.Pi2dWinding
  using (wstep; wind; wind-++2; wstep-cancel)

--------------------------------------------------------------------------------
-- §1. 逆步的位移：另一方向的抵消（`wstep-cancel` 的**换序**版）
--------------------------------------------------------------------------------

wstep-inv-sum : ∀ {G : DiGraph} {u v : V G} {p q : Walk G u v} (s : AStep G p q)
              → wstep (invAStep s) + wstep s ≡ + 0
wstep-inv-sum (slide  _ _ _ _ _) = refl
wstep-inv-sum (expand _ _ _ _ _) = refl

--------------------------------------------------------------------------------
-- §2. ★★ 相干律：`wind` 把 `rev2` 看成取负
--------------------------------------------------------------------------------

-- 先把 `rev2 (cons2 s c)` 的位移规约成 `wind (rev2 c) + wstep (invAStep s)`
rev2-wind-form : ∀ {G : DiGraph} {x : V G} {w1 wm w2 : Walk G x x}
                 (s : AStep G w1 wm) (c : Ω2Walk G x wm w2)
               → wind (rev2 (cons2 s c))
                 ≡ wind (rev2 c) + wstep (invAStep s)
rev2-wind-form {G} {x} {w1} {wm} {w2} s c =
  trans (wind-++2 (rev2 c) (cons2 (invAStep s) (nil2 _)))
        (cong (λ z → wind (rev2 c) + z) (+-identityʳ (wstep (invAStep s))))

wind-rev2 : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
            (c : Ω2Walk G x w1 w2)
          → wind (rev2 c) + wind c ≡ + 0
wind-rev2 (nil2 w) = refl

wind-rev2 {G} {x} {w1} (cons2 {w1} {wm} {w2} s c) =
  -- 记 `A = wind (rev2 c)`、`b = wstep (invAStep s)`、`a = wstep s`、`C = wind c`
  -- 目标：`(A + b) + (a + C) ≡ +0`；已知 `b + a ≡ +0`（`wstep-inv-sum`）与 `A + C ≡ +0`（IH）
  trans (cong (λ z → z + wind (cons2 s c)) (rev2-wind-form s c))
        (trans (+-assoc (wind (rev2 c)) (wstep (invAStep s)) (wstep s + wind c))
        (trans (cong (λ z → wind (rev2 c) + z)
                     (sym (+-assoc (wstep (invAStep s)) (wstep s) (wind c))))
        (trans (cong (λ z → wind (rev2 c) + z)
                     (cong (λ z → z + wind c) (wstep-inv-sum s)))
        (trans (cong (λ z → wind (rev2 c) + z) (+-identityˡ (wind c)))
               (wind-rev2 c)))))
