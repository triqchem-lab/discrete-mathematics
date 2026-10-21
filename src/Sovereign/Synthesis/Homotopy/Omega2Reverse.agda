{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Omega2Reverse
--
-- **`Ω2Walk` 的显式逆** —— `π₂ᵈ⁺` 从幺半群作用升级为**群作用**的关键一步
--
-- ## 为什么这一层能做到一阶做不到的事
--
-- 一阶的 `rev-cancel`（`AStepStdGroup`）**没做完**：`AHomotopyStd` 里消 `s ∘ s⁻¹`
-- 只有 `bt`（只在前缀位直接可用），中途要做大量 `++w-assoc` 运输。
--
-- **二阶不一样**：`Ω3Walk⁺` 的 `bub3` 构造子**天生就是「任意位」消去**：
-- ```
--   bub3 c₁ s c₂ : Ω3Step⁺ ((c₁ ++2 bub s) ++2 c₂) (c₁ ++2 c₂)
-- ```
-- 而 `bub s = cons2 s (cons2 (invAStep s) (nil2 _))` 正是「走一步再退一步」。
-- ⇒ `rev2-cancel` 只需**一次**前缀缘饰 + **一次** `bub3`，不需要显式搬位置。
--
-- ## 核心定理
--
-- ```
--   rev2        : Ω2Walk G x w1 w2 → Ω2Walk G x w2 w1      （反转步序 + 每步取逆）
--   rev2-cancel : Ω3Walk⁺ G x (c ++2 rev2 c) (nil2 w1)     （走与反向可消）
-- ```
--
-- ⇒ `π₂ᵈ⁺` 的 `_++2_` 意义下每个 2-走都有逆 ⇒ 结构从幺半群作用升级为**群作用**。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用全部既有件：`whisk-resp` / `suffix-resp` / `subst₂-Ω3Walk⁺` / `bub3`
--   · 不引入对称化假设（路线 b 的优势）

module Sovereign.Synthesis.Homotopy.Omega2Reverse where

-- 纯限定导入：PE 的全部名字只经 PPE.x 访问（`open import ... as` 会同时带进无前缀作用域）
import Relation.Binary.PropositionalEquality as PPE
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil)
open DiGraph using (V)
open import Sovereign.Synthesis.Homotopy.Omega2
  using (Ω2Walk; nil2; cons2; _++2_; ++2-assoc)
open import Sovereign.Synthesis.Homotopy.Omega3
  using (invAStep)
open import Sovereign.Synthesis.Homotopy.Omega3Plus
  using (Ω3Walk⁺; refl3+; trans3+; gen3+; bub3; bub)
open import Sovereign.Synthesis.Homotopy.Omega3Suffix
  using (whisk-resp; suffix-resp; subst₂-Ω3Walk⁺)

--------------------------------------------------------------------------------
-- §1. 反向 2-走：反转步序 + 每步取逆
--------------------------------------------------------------------------------

rev2 : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
     → Ω2Walk G x w1 w2 → Ω2Walk G x w2 w1
rev2 (nil2 w)    = nil2 w
rev2 (cons2 s c) = rev2 c ++2 cons2 (invAStep s) (nil2 _)

--------------------------------------------------------------------------------
-- §2. ★★ 走与它的反向可消
--
-- `cons2 s c` 情形：
--   ① IH：`c ++2 rev2 c ⁓ nil2`
--   ② 右缘饰 `e = cons2 (invAStep s) (nil2 _)`：`(c ++2 rev2 c) ++2 e ⁓ e`
--   ③ 结合律运输：`c ++2 (rev2 c ++2 e) ⁓ e`
--   ④ 左缘饰 `cons2 s (nil2 _)`：`cons2 s (c ++2 rev2 c ++2 e) ⁓ cons2 s e`（= `bub s`）
--   ⑤ `bub3`：`bub s ⁓ nil2`
--------------------------------------------------------------------------------

rev2-cancel : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
              (c : Ω2Walk G x w1 w2)
            → Ω3Walk⁺ G x (c ++2 rev2 c) (nil2 w1)
rev2-cancel (nil2 w) = refl3+ _

rev2-cancel {G} {x} {w1} (cons2 {w1} {wm} {w2} s c) =
    trans3+ (whisk-resp (cons2 s (nil2 _)) step1)
            (gen3+ (bub3 (nil2 _) s (nil2 _)))
  where
    e : Ω2Walk G x wm w1
    e = cons2 (invAStep s) (nil2 w1)

    -- ★ 显式桥引理：把 `rev2 (cons2 s c)` 与 `rev2 c ++2 e` 的差别**写出来**。
    -- 关键：类型写成语义两个端点（左边用 `rev2 (cons2 s c)`，右边用结合形），
    -- Agda 靠**转换检查**接受 `++2-assoc`（而不是靠 `cong` 的语法匹配）✓
    assocF : (c ++2 rev2 c) ++2 e ≡ c ++2 rev2 (cons2 s c)
    assocF = ++2-assoc c (rev2 c) e

    step1 : Ω3Walk⁺ G x (c ++2 rev2 (cons2 s c)) e
    step1 = subst₂-Ω3Walk⁺ assocF PPE.refl (suffix-resp e (rev2-cancel c))
