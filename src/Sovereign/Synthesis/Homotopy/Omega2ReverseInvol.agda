{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Omega2ReverseInvol
--
-- **右逆**：`rev2 c ++2 c ⁓ nil` ⇒ `π₂ᵈ⁺` 从「幺半群 + 左逆」升级为**群**
--
-- ## 路线
--
-- 由 `rev2-cancel` 在 `rev2 c` 上取：`rev2 c ++2 rev2 (rev2 c) ⁓ nil`。
-- ⇒ 只需把 `rev2 (rev2 c)` 换成 `c`，即证**对合** `rev2-invol : rev2 (rev2 c) ≡ c`。
--
-- 而对合需要 `rev2` 对 `++2` 的**分配律**：
--
-- ```
--   rev2-dist : rev2 (a ++2 b) ≡ rev2 b ++2 rev2 a     -- 反序分配
-- ```
--
-- 两层都是结构归纳，各只需**一次** `++2-assoc` / `++2-nilR` 的命题改写。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · **零 Cubical**（纯 PropEq）
--   · 复用 `rev2` / `rev2-cancel` / `++2-assoc` / `invAStep-invol` / `cong₂-Ω3`

module Sovereign.Synthesis.Homotopy.Omega2ReverseInvol where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; AStep)
open DiGraph using (V)
open import Sovereign.Synthesis.Homotopy.Omega2
  using (Ω2Walk; nil2; cons2; _++2_; ++2-nilR; ++2-assoc)
open import Sovereign.Synthesis.Homotopy.Omega3
  using (invAStep; invAStep-invol)
open import Sovereign.Synthesis.Homotopy.Omega3Plus
  using (Ω3Walk⁺; refl3+; trans3+)
open import Sovereign.Synthesis.Homotopy.Omega3Suffix using (≡→Ω3Walk⁺)
open import Sovereign.Synthesis.Homotopy.Omega2Reverse using (rev2; rev2-cancel)
open import Sovereign.Synthesis.Homotopy.Pi2dFunctionLayer using (cong₂-Ω3)

--------------------------------------------------------------------------------
-- §1. ★ 反序分配律：`rev2 (a ++2 b) ≡ rev2 b ++2 rev2 a`
--------------------------------------------------------------------------------

rev2-dist : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 : Walk G x x}
            (a : Ω2Walk G x w1 w2) (b : Ω2Walk G x w2 w3)
          → rev2 (a ++2 b) ≡ rev2 b ++2 rev2 a
rev2-dist (nil2 w) b = sym (++2-nilR (rev2 b))
rev2-dist (cons2 s a) b =
  trans (cong (λ z → z ++2 cons2 (invAStep s) (nil2 _)) (rev2-dist a b))
        (++2-assoc (rev2 b) (rev2 a) (cons2 (invAStep s) (nil2 _)))

--------------------------------------------------------------------------------
-- §2. ★ 对合：`rev2 (rev2 c) ≡ c`
--
-- 辅助件：`rev2 (cons2 (invAStep s) (nil2 _)) ≡ cons2 s (nil2 _)`
-- —— 靠 `invAStep-invol`（`Omega3`）+ `rev2` 在单步上的展开（定义性）。
--------------------------------------------------------------------------------

rev2-inv-step : ∀ {G : DiGraph} {x : V G} {w1 wm : Walk G x x}
                (s : AStep G w1 wm)
              → rev2 (cons2 (invAStep s) (nil2 _)) ≡ cons2 s (nil2 _)
rev2-inv-step s = cong (λ t → cons2 t (nil2 _)) (invAStep-invol s)

rev2-invol : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
             (c : Ω2Walk G x w1 w2) → rev2 (rev2 c) ≡ c
rev2-invol (nil2 w) = refl
rev2-invol (cons2 s c) =
  trans (rev2-dist (rev2 c) (cons2 (invAStep s) (nil2 _)))
        (trans (cong (λ z → rev2 (cons2 (invAStep s) (nil2 _)) ++2 z)
                     (rev2-invol c))
               (trans (cong (λ t → cons2 t (nil2 _) ++2 c)
                            (invAStep-invol s))
                      refl))

--------------------------------------------------------------------------------
-- §3. ★★ 右逆：`rev2 c ++2 c ⁓ nil`（名字避开 `CayleyMetric.inv-right`）
--------------------------------------------------------------------------------

inv-right-Ω3 : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
            (c : Ω2Walk G x w1 w2)
          → Ω3Walk⁺ G x (rev2 c ++2 c) (nil2 w2)
inv-right-Ω3 c =
  trans3+ (cong₂-Ω3 (refl3+ (rev2 c)) (≡→Ω3Walk⁺ (sym (rev2-invol c))))
          (rev2-cancel (rev2 c))
