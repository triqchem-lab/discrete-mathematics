{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6AStepCode2
--
-- **④ 探针的修正**：`AStepCode` 需要**六**组件，不是三组件
--
-- ## 我上批漏了什么（已查 `BarceloAHomotopy.agda:50-56` 的真实定义）
--
-- ```
--   slide  : ∀ {u x y z v} (p : Walk G u x) (b : Walk G z v)
--          → (e1 : edge G x y) (e2 : edge G y z) (e3 : edge G x z)
--          → AStep G (p ++w (cons e1 (cons e2 b))) (p ++w (cons e3 b))
-- ```
-- ⇒ 一步的**显式参数**是 `p`、`b`、**`e1`、`e2`、`e3`** 共 5 个。
--   我上批的码 `ADir × CWalk × CWalk` **只码了 `p` 和 `b`**，**漏了中间三条边** ✗
--
-- ## 修正后的码
--
-- ```
--   StepCode n = ADir × CWalk n × CStep n × CStep n × CStep n × CWalk n
--                （方向，前缀，e1，e2，e3，后缀）
-- ```
-- 其中每条边用 **`CStep`**（方向 + 坐标）码 —— 因为**给定起点顶点，
-- 一条边由「方向 + 坐标」唯一确定，且见证是 `refl`**
-- （与 `T6CayleyCodeWalk.cEdge` 同一手法）✓
--
-- ## ★ 一个好消息（比上批更乐观的部分）
--
-- 中间三条边既然是**显式参数**，就不需要「在图中搜索三角形」
-- ⇒ 码 → 步的映射**不需要 `Maybe`**（前提是码里带足分量 + 起点）✓
-- 这比上批记的「需搜索、需 `Maybe`」要好。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyCode` 的 `CStep`/`CWalk`/`DecEq-CStep`/`DecEq-CWalk` 与 `T6AStepCode.ADir`

module Sovereign.Synthesis.Homotopy.T6AStepCode2 where

open import Data.Nat using (ℕ)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import Sovereign.Synthesis.Homotopy.T6CayleyCode
  using (CStep; CWalk; DecEq-CStep; DecEq-CWalk)
open import Sovereign.Synthesis.Homotopy.T6AStepCode using (ADir; DecEq-ADir)

--------------------------------------------------------------------------------
-- §1. 六组件码（构造子形式，方便 `cong` 链）
--------------------------------------------------------------------------------

data StepCode (n : ℕ) : Set where
  mkStep : (dir : ADir) (pref : CWalk n)
           (e1 e2 e3 : CStep n) (suff : CWalk n)
         → StepCode n

--------------------------------------------------------------------------------
-- §2. ★★ 可判定相等（6 层 `with` + 6 个 `cong` 的一条 `trans` 链）
--------------------------------------------------------------------------------

DecEq-StepCode : ∀ {n : ℕ} (s s' : StepCode n) → Dec (s ≡ s')
DecEq-StepCode (mkStep d w a b c f) (mkStep d' w' a' b' c' f')
  with DecEq-ADir d d'
... | no  ¬p = no λ { refl → ¬p refl }
... | yes p1 with DecEq-CWalk w w'
...   | no  ¬p = no λ { refl → ¬p refl }
...   | yes p2 with DecEq-CStep a a'
...     | no  ¬p = no λ { refl → ¬p refl }
...     | yes p3 with DecEq-CStep b b'
...       | no  ¬p = no λ { refl → ¬p refl }
...       | yes p4 with DecEq-CStep c c'
...         | no  ¬p = no λ { refl → ¬p refl }
...         | yes p5 with DecEq-CWalk f f'
...           | no  ¬p = no λ { refl → ¬p refl }
...           | yes p6 =
  yes (trans (cong (λ z → mkStep z w a b c f) p1)
       (trans (cong (λ z → mkStep d' z a b c f) p2)
       (trans (cong (λ z → mkStep d' w' z b c f) p3)
       (trans (cong (λ z → mkStep d' w' a' z c f) p4)
       (trans (cong (λ z → mkStep d' w' a' b' z f) p5)
              (cong (λ z → mkStep d' w' a' b' c' z) p6))))))

--------------------------------------------------------------------------------
-- §3. ⬜ 下一步（判据明确）
--
-- ① **码 → 步的映射**（**不需要 `Maybe`**，见上）：
--    `toStep : (x : T6Vec n) (c : StepCode n)
--            → Maybe (Σ (λ (p q : Walk (T6CayleySym n) ? ?) → AStep (T6CayleySym n) p q))`
--    用 `T6CayleyCodeWalk.cEdge`（见证 = `refl`）把三个 `CStep` 变成三条边；
--    ⚠ 仍需起点顶点推出 `x, y, z` 的坐标 —— 但那是**计算**（`ctarget`），不是搜索 ✓
-- ② **单射性**：码相等 ⇒ 步相等（需证明 `toStep` 在有效码上单射）。
--
-- 本模块只交码与可判定相等；映射与单射性未做。
--------------------------------------------------------------------------------
