{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6AStepCode
--
-- **④ 的可行性探针**：`ASTep` 的二级码 —— 绕开 `uip` 的形状
--
-- ## 问的问题
--
-- ④（`π₂ᵈ⁺` 精确刻画）的障碍之一是：`DecEq (ASTep …)` 需要比较 `edge` 见证 ⇒ 需 `uip`。
-- 本模块回答：**这个障碍有绕过形状吗？**
--
-- ## 答案：有，且形状清楚
--
-- `ASTep` 的构造子是
-- ```
--   slide  : ∀ {u x y z v} (p : Walk G u x) (b : Walk G z v) → …
--   expand : ∀ {u x y z v} (p : Walk G u x) (b : Walk G z v) → …
-- ```
-- ⇒ **一步 = 方向 + 前缀走 + 后缀走**，三者都**不含证明分量**
--   （走用码 `CWalk` 表示即可）。
--
-- ⇒ 二级码：
-- ```
--   data ADir : Set where dslide dexpand : ADir
--   AStepCode n = ADir × CWalk n × CWalk n
-- ```
-- ⇒ `DecEq-AStepCode` 是**平凡的**（`ADir` 两构造子 + `CWalk` 已可判定）
--   —— **完全不用 `uip`** ✓
--
-- ## ⚠ 探针的**诚实边界**（不是「形状清楚」就等于「已解决」）
--
-- `slide` 自带**侧条件**：它要求中间的那条边 `(x , z)` 存在。
-- 码不携带这个侧条件 ⇒
--
-- | 命题 | 状态 |
-- |---|---|
-- | 码层存在且相等可判定 | ✅ **本模块已证** |
-- | 码 → `ASTep` 的映射存在 | ✅ **已证**：`T6AStepCodeMap.toStepCode` / `toStepCodeExpand`（双向）/ `toAHomotopyDir`（`ADir` 分派）|
-- | 「码相等 ⇒ 步相等」 | ✅ **平凡成立**（`toStepCode` 是码的函数 ⇒ `cong`）；**忠实性**（不同码 ⇒ 不同步）仍未做 |
--
-- ⇒ **结论：④ 的 `DecEq` 障碍不是死路，但代价是引入侧条件 + 一条单射性**。
--   「代价可接受与否」是路线判断 ⇒ 不在此下结论（见 `AGENTS.md`「路线判断也要标推测」）。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyCode` 的 `CStep`/`CWalk`/`DecEq-CStep`/`DecEq-CWalk`（不重写）

module Sovereign.Synthesis.Homotopy.T6AStepCode where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import Sovereign.Synthesis.Homotopy.T6CayleyCode
  using (CStep; CWalk; DecEq-CStep; DecEq-CWalk)

--------------------------------------------------------------------------------
-- §1. 方向 + 二级码
--------------------------------------------------------------------------------

data ADir : Set where
  dslide  : ADir
  dexpand : ADir

-- ★ 一步的码：方向 + 前缀走码 + 后缀走码（**无证明分量**）
AStepCode : ℕ → Set
AStepCode n = ADir × CWalk n × CWalk n

--------------------------------------------------------------------------------
-- §2. ★★ 码的可判定相等（平凡：两构造子 + 已可判定件，**不用 uip**）
--------------------------------------------------------------------------------

DecEq-ADir : (d d' : ADir) → Dec (d ≡ d')
DecEq-ADir dslide  dslide  = yes refl
DecEq-ADir dslide  dexpand = no λ ()
DecEq-ADir dexpand dslide  = no λ ()
DecEq-ADir dexpand dexpand = yes refl

-- 具体类型上直接展开（不写泛型 `DecEq-×` —— 实测泛型版会撞类型层级）
DecEq-AStepCode : ∀ {n : ℕ} (s s' : AStepCode n) → Dec (s ≡ s')
DecEq-AStepCode (d , (a , b)) (d' , (a' , b')) with DecEq-ADir d d'
... | no  ¬p = no λ { refl → ¬p refl }
... | yes p  with DecEq-CWalk a a'
...   | no  ¬q = no λ { refl → ¬q refl }
...   | yes q  with DecEq-CWalk b b'
...     | no  ¬r = no λ { refl → ¬r refl }
...     | yes r  = yes (trans (cong (λ z → z , (a , b)) p)
                              (cong (λ z → d' , z) (cong₂ _,_ q r)))

--------------------------------------------------------------------------------
-- §3. ⬜ 探针**未**回答的（如实列出，不冒充结论）
--
-- ① **码 → `ASTep` 的影射**：
--    `toStep : (x : T6Vec n) → AStepCode n → Maybe (ASTep (T6CayleySym n) ? ?)`
--    —— 需要用 `T6CayleyCodeWalk.interpC` 把两个 `CWalk` 译成 `Walk`，
--       再构造 `slide`/`expand`；但 `slide` 要求中间边存在 ⇒ 可能返回 `nothing`。
-- ② **单射性**：有效码上 `toStep` 单射（⇒ 码相等推出步相等）。
-- ③ 然后才能把码层的判定搬到 `ASTep` 上，进而给 `reduce` 用。
--
-- ⇒ 「这三步要多少工作量」是**路线判断**，本模块不下结论。
--------------------------------------------------------------------------------
