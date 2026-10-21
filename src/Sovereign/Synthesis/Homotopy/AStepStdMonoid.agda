{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.AStepStdMonoid
--
-- **PIO-2 正式化（一）：`AStepStd` 的拼接上下文** —— A1:13 反截断四要件的第 ④ 项
--
-- ## 八要素 / 反截断四要件的对表（本模块负责 ④）
--
-- `docs/plan/A1-pi-n-paths-abcd-research.md:13` 的宪法级反截断要求：
-- 候选定义**必须保留 ①群层载具 ②生成元 ③关系（复合/逆）④拼接上下文**。
--
-- | 要件 | `AStepStd` 侧 | 本模块 |
-- |---|---|---|
-- | ① 载具 | `Walk G u v` | —（类型即载具）|
-- | ② 生成元 | `tri-slide` / `sq-slide4` / `bt` 三类 | —（`data` 三构造子）|
-- | ③ 关系 | `AHomotopyStd`（`rfl`/`sym`/`trn`/`gen`）| — |
-- | **④ 拼接上下文** | `_++w_` 的**左右同余** | ✅ **本模块** |
--
-- ## 本模块证什么
--
-- ```agda
-- AStepStd-++w   : AStepStd G p q → AStepStd G (p ++w r) (q ++w r)      -- 右同余
-- AStepStd-++wˡ  : AStepStd G p q → AStepStd G (r ++w p) (r ++w q)      -- 左同余
-- AHStd-++w / AHStd-++wˡ : 同上，但到 AHomotopyStd 层
-- AHStd-cong     : AHomotopyStd G p p' → AHomotopyStd G q q'
--                → AHomotopyStd G (p ++w q) (p' ++w q')                -- 乘法同余
-- ```
--
-- ⇒ `AHomotopyStd` 关于 `_++w_` 是**同余** ⇒ 商 `Walk G v v / AHomotopyStd`
-- 承载**幺半群**结构（同 `π₁ᵈ` 的 `Pi1dMonoid`）✓
--
-- ## ⚠ 只用到 `++w-assoc`，不需要结合律以外的任何东西
--
-- 三个生成元在右乘/左乘下结构不变，只差一层 `++w-assoc` 的运输
-- （与 `Pi1dMonoid.AStep-++w` 完全同构的手法）。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `Pi1dMonoid` 的 `++w-assoc`（不重证）

module Sovereign.Synthesis.Homotopy.AStepStdMonoid where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_)
open DiGraph using (V)
open import Sovereign.Synthesis.Homotopy.Pi1dMonoid
  using (++w-assoc)
-- ⚠ `using` 与 `renaming` 不能同时点名同一符号（RepeatedNamesInImportDirective）
--   ⇒ 只写 renaming，把 AHomotopyStd 的 `sym` 改名以避与 PropEq 的 `sym` 撞名
open import Sovereign.Synthesis.Homotopy.AStepStd renaming (sym to sym')

--------------------------------------------------------------------------------
-- §1. 二元 `subst`（`AStepStd` 是端点依赖的关系，但两端端点相同 ⇒ 可用朴素版）
--------------------------------------------------------------------------------

subst-AStepStd : ∀ {G : DiGraph} {u v : V G}
                 {a a' b b' : Walk G u v}
               → a ≡ a' → b ≡ b' → AStepStd G a b → AStepStd G a' b'
subst-AStepStd refl refl z = z

--------------------------------------------------------------------------------
-- §2. ★ 右同余：`AStepStd` 在 `_++w_` 右乘下稳定
--------------------------------------------------------------------------------

AStepStd-++w : ∀ {G : DiGraph} {u v w : V G} {p q : Walk G u v}
               (r : Walk G v w)
             → AStepStd G p q → AStepStd G (p ++w r) (q ++w r)

AStepStd-++w r (tri-slide p b e1 e2 e3) =
  subst-AStepStd (sym (++w-assoc p (cons e1 (cons e2 b)) r))
                 (sym (++w-assoc p (cons e3 b) r))
                 (tri-slide p (b ++w r) e1 e2 e3)

AStepStd-++w r (sq-slide4 p b e1 e2 e3 e4) =
  subst-AStepStd (sym (++w-assoc p (cons e1 (cons e2 (cons e3 b))) r))
                 (sym (++w-assoc p (cons e4 b) r))
                 (sq-slide4 p (b ++w r) e1 e2 e3 e4)

AStepStd-++w r (bt p q e f) =
  subst-AStepStd (sym (++w-assoc p (cons e (cons f q)) r))
                 (sym (++w-assoc p q r))
                 (bt p (q ++w r) e f)

--------------------------------------------------------------------------------
-- §3. ★ 左同余：`AStepStd` 在 `_++w_` 左乘下稳定
--------------------------------------------------------------------------------

AStepStd-++wˡ : ∀ {G : DiGraph} {u v w : V G} {p q : Walk G v w}
                (r : Walk G u v)
              → AStepStd G p q → AStepStd G (r ++w p) (r ++w q)

AStepStd-++wˡ r (tri-slide p b e1 e2 e3) =
  subst-AStepStd (++w-assoc r p (cons e1 (cons e2 b)))
                 (++w-assoc r p (cons e3 b))
                 (tri-slide (r ++w p) b e1 e2 e3)

AStepStd-++wˡ r (sq-slide4 p b e1 e2 e3 e4) =
  subst-AStepStd (++w-assoc r p (cons e1 (cons e2 (cons e3 b))))
                 (++w-assoc r p (cons e4 b))
                 (sq-slide4 (r ++w p) b e1 e2 e3 e4)

AStepStd-++wˡ r (bt p q e f) =
  subst-AStepStd (++w-assoc r p (cons e (cons f q)))
                 (++w-assoc r p q)
                 (bt (r ++w p) q e f)

--------------------------------------------------------------------------------
-- §4. 提升到等价闭包层
--------------------------------------------------------------------------------

AHStd-++w : ∀ {G : DiGraph} {u v w : V G} {p q : Walk G u v}
            (r : Walk G v w)
          → AHomotopyStd G p q → AHomotopyStd G (p ++w r) (q ++w r)
AHStd-++w r (rfl p)         = rfl (p ++w r)
AHStd-++w r (sym' h)        = sym' (AHStd-++w r h)
AHStd-++w r (trn h1 h2)     = trn (AHStd-++w r h1) (AHStd-++w r h2)
AHStd-++w r (gen st)        = gen (AStepStd-++w r st)

AHStd-++wˡ : ∀ {G : DiGraph} {u v w : V G} {p q : Walk G v w}
             (r : Walk G u v)
           → AHomotopyStd G p q → AHomotopyStd G (r ++w p) (r ++w q)
AHStd-++wˡ r (rfl p)        = rfl (r ++w p)
AHStd-++wˡ r (sym' h)       = sym' (AHStd-++wˡ r h)
AHStd-++wˡ r (trn h1 h2)    = trn (AHStd-++wˡ r h1) (AHStd-++wˡ r h2)
AHStd-++wˡ r (gen st)       = gen (AStepStd-++wˡ r st)

--------------------------------------------------------------------------------
-- §5. ★★ 乘法同余 ⇒ 商 `Walk G v v / AHomotopyStd` 是**幺半群**
--------------------------------------------------------------------------------

AHStd-cong : ∀ {G : DiGraph} {u v w : V G}
             {p p' : Walk G u v} {q q' : Walk G v w}
           → AHomotopyStd G p p' → AHomotopyStd G q q'
           → AHomotopyStd G (p ++w q) (p' ++w q')
AHStd-cong {q = q} {q' = q'} h1 h2 =
  trn (AHStd-++w q h1) (AHStd-++wˡ _ h2)
