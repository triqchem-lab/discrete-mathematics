{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.AStepStdGroup
--
-- **反向关系（逆）在 `AStepStd` 口径下的进展 —— 部分完成，边界明写**
--
-- ## 这一件要做到什么
--
-- `A1:13` 反截断四要件 ③ 是「关系（复合 / **逆**）」。`AStepStdMonoid` 已给出
-- ④ 拼接上下文（左右同余 + 乘法同余）。本模块处理 ③ 的「逆」。
--
-- ## 已证（本模块）
--
-- | 项 | 内容 |
-- |---|---|
-- | `rev` 的展开律 | `rev (cons e (nil _)) = cons (sym-edge e) (nil _)`（定义性）✓ |
-- | `rev` | 把走倒过来：`Walk G u v → Walk G v u` ✓ |
-- | `rev-cancel-one` | **长度 1 的走层逆**：`(x→y) ++ (x→y)⁻¹ ⁓ nil`（一条 `bt`）✓ |
--
-- ## ⬜ 未证（如实标注，不冒充）
--
-- `rev-cancel`（**一般**的走层逆）：
-- `∀ (p : Walk G u v) → AHomotopyStd G (p ++w rev p) (nil u)`
--
-- 证明草图（我用归纳推过，结构清楚但传输较多，本轮未写完）：
-- 对 `p` 归纳。`p = cons e' p'` 时，
-- `p' ++w (rev (cons e' p') ++w cons (sym-edge e) nil)`
--   ≡ `p' ++w ((rev p' ++w cons (sym-edge e') nil) ++w cons (sym-edge e) nil)`
--   ⁓ `cons (sym-edge e') nil ++w cons (sym-edge e) nil`   （IH + 右同余 + `++w-assoc` 运输）
--   = `cons (sym-edge e') (cons (sym-edge e) nil)`
-- ⇒ 外面套 `cons e'` 后一条 `bt` 消掉 ⇒ `⁓ cons (sym-edge e) nil`。
-- 需要两次 `subst`（`sym (++w-assoc …)`）与 `prefix-cong`。
--
-- **⇒ 本模块不声称「`π₁ᵈˢᵗᵈ` 是群」**（那需要一般 `rev-cancel`）。
--   已证的是：**边层逆 + 长度 1 的走层逆**。
--
-- ## 核心原则
--   · 0 postulate / 0 hole（未证的不写成定理，只在注释里留草图）
--   · 复用 `AStepStdMonoid` 的同余引理（不重证）

module Sovereign.Synthesis.Homotopy.AStepStdGroup where

open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_)
open DiGraph using (V; edge)
open import Sovereign.Synthesis.Homotopy.Pi1dMonoid using (++w-assoc)
open import Sovereign.Synthesis.Homotopy.AStepStd renaming (sym to sym')
open import Sovereign.Synthesis.Homotopy.AStepStdMonoid
  using (AHStd-++w; AHStd-++wˡ; AHStd-cong)

--------------------------------------------------------------------------------
-- §1. 关系层的运输与前缀同余
--------------------------------------------------------------------------------

subst-AHStd : ∀ {G : DiGraph} {u v : V G} {a a' b b' : Walk G u v}
            → a ≡ a' → b ≡ b' → AHomotopyStd G a b → AHomotopyStd G a' b'
subst-AHStd refl refl z = z

-- 前缀同余：由左同余**定义性**得到（`cons e X = cons e (nil _) ++w X`）
prefix-cong : ∀ {G : DiGraph} {u v a : V G} (e : edge G u a)
              {X Y : Walk G a v}
            → AHomotopyStd G X Y → AHomotopyStd G (cons e X) (cons e Y)
prefix-cong e h = AHStd-++wˡ (cons e (nil _)) h

--------------------------------------------------------------------------------
-- §2. 反向走
--------------------------------------------------------------------------------

module _ {G : DiGraph} (sym-edge : ∀ {x y : V G} → edge G x y → edge G y x) where

  rev : ∀ {u v : V G} → Walk G u v → Walk G v u
  rev (nil v)    = nil v
  rev (cons e p) = rev p ++w cons (sym-edge e) (nil _)

  -- ★ 长度 1 的走层逆：`(x→y) ++ (x→y)⁻¹ ⁓ nil` —— 一条 `bt` 就够
  --
  -- `rev (cons e (nil _)) = nil _ ++w cons (sym-edge e) (nil _) = cons (sym-edge e) (nil _)`
  -- ⇒ 左边定义性地是 `cons e (cons (sym-edge e) (nil _))`，正是 `bt` 的源 ✓
  rev-cancel-one : ∀ {u v : V G} (e : edge G u v)
                 → AHomotopyStd G ((cons e (nil v)) ++w rev (cons e (nil v))) (nil u)
  rev-cancel-one e = gen (bt (nil _) (nil _) e (sym-edge e))
