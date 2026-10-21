{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.AStepStd
--
-- **标准 A-同伦的生成元层**：`AStepStd` = 三角移动 ∪ 方形移动 ∪ 回溯
--
-- ## 来源与定位
--
-- 台账 `PIO-1.boundary.pi1d-vs-barcelo`（口径差裁决）与 `PIO-1.fix.astep-std`（修复件①）
-- 指出：库的 `AStep` **只有三角形** `slide`/`expand`，缺
--
--   ① **方形移动**（4-循环 2-胞腔）—— 标准 A-同伦（Morrill 1905.06049 §2）含之；
--   ② **回溯移动**（`x→y→x` 可消）—— 标准 A-同伦含之。
--
-- 本模块把这三类生成元与它们的等价闭包**从探针 `_PEH32` 提升为正式件** ✓
-- （探针只作草稿；正式件在 `src/` 下，有编译回执、进台账）。
--
-- ## ⚠ 与 `AHomotopy` 的关系（不要混）
--
-- | 关系 | 含义 |
-- |---|---|
-- | `AH⊆AHStd` | `AHomotopy ⊆ AHomotopyStd`（三角移动是标准移动的特例）✓ |
-- | 反向 **不成立** | `AStepStd` 比 `AStep` **强**：它会多粘合走 ⇒ 商更小。 |
--
-- ⇒ `π₁ᵈ`（三角口径）与 `π₁ᵈˢᵗᵈ`（标准口径）是**两个不同的商对象**，
--   不是同一个东西的两种写法 ✗。`AH→≡`（无三角形时塌缩为相等）只在 `AHomotopy` 侧成立。
--
-- ## 关键事实（本模块只给定义层 + 包含关系；具体图形的坍缩定理另立）
--
-- 回溯移动需要图里存在**一对对易边** `e : x→y`、`f : y→x`。
-- ⇒ 若 Cayley 图只含 `+e_j` 生成元（如 `T6Cayley`），**`bt` 不可用**，
--   即便加了方形移动也不会额外塌缩；要塌缩必须让生成元集含 `±e_j`（对称化）。
--   这一点是裁决「三步归零 ⇒ π₁ᵈ ≅ C₃」的必要前提，已写入 journal 待裁决。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 复用 `BarceloAHomotopy` 的 `DiGraph`/`Walk`/`_++w_`（不重写）

module Sovereign.Synthesis.Homotopy.AStepStd where

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AStep; slide; expand; AHomotopy;
         refl'; symm; trans'; gen)
open DiGraph using (V; edge)

--------------------------------------------------------------------------------
-- §1. 标准 A-同伦的生成元
--------------------------------------------------------------------------------

data AStepStd (G : DiGraph) : ∀ {u v} → Walk G u v → Walk G u v → Set where

  -- ① 三角移动（与 `AStep` 的 `slide` 逐字相同）
  tri-slide : ∀ {u x y z v} (p : Walk G u x) (b : Walk G z v)
            → (e1 : edge G x y) (e2 : edge G y z) (e3 : edge G x z)
            → AStepStd G (p ++w (cons e1 (cons e2 b))) (p ++w (cons e3 b))

  -- ② 方形移动（4-循环 2-胞腔）：三条边 `x→y→z→w` 换成对角 `x→w`
  sq-slide4 : ∀ {u x y z w v} (p : Walk G u x) (b : Walk G w v)
            → (e1 : edge G x y) (e2 : edge G y z) (e3 : edge G z w)
            → (e4 : edge G x w)
            → AStepStd G (p ++w (cons e1 (cons e2 (cons e3 b)))) (p ++w (cons e4 b))

  -- ③ 回溯：`x→y→x` 可消
  bt        : ∀ {u x y v} (p : Walk G u x) (q : Walk G x v)
            → (e : edge G x y) (f : edge G y x)
            → AStepStd G (p ++w (cons e (cons f q))) (p ++w q)

--------------------------------------------------------------------------------
-- §2. 等价闭包
--------------------------------------------------------------------------------

data AHomotopyStd (G : DiGraph) : ∀ {u v} → Walk G u v → Walk G u v → Set where
  rfl : ∀ {u v} (w : Walk G u v) → AHomotopyStd G w w
  sym : ∀ {u v} {w1 w2 : Walk G u v} → AHomotopyStd G w1 w2 → AHomotopyStd G w2 w1
  trn : ∀ {u v} {w1 w2 w3 : Walk G u v}
      → AHomotopyStd G w1 w2 → AHomotopyStd G w2 w3 → AHomotopyStd G w1 w3
  gen : ∀ {u v} {w1 w2 : Walk G u v} → AStepStd G w1 w2 → AHomotopyStd G w1 w2

--------------------------------------------------------------------------------
-- §3. ★ 包含关系：三角口径 ⊆ 标准口径
--
-- ⚠ `expand` 是 `slide` 的**逆向**，而 `AStepStd` 只有 `tri-slide` 一个方向
--   ⇒ 必须在**闭包层**用 `sym` 转过来（探针 `_PEH32:83-89` 已踩过这一点）。
--------------------------------------------------------------------------------

AH⊆AHStd : ∀ (G : DiGraph) {u v} {w1 w2 : Walk G u v}
         → AHomotopy G w1 w2 → AHomotopyStd G w1 w2
AH⊆AHStd G (refl' w)                     = rfl w
AH⊆AHStd G (symm h)                      = sym (AH⊆AHStd G h)
AH⊆AHStd G (trans' h1 h2)                = trn (AH⊆AHStd G h1) (AH⊆AHStd G h2)
AH⊆AHStd G (gen (slide  p b e1 e2 e3))   = gen (tri-slide p b e1 e2 e3)
AH⊆AHStd G (gen (expand p b e1 e2 e3))   = sym (gen (tri-slide p b e1 e2 e3))
