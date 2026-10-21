{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.Omega2
--
-- **`Ω²` 定义层正式化** —— 第六层（高阶同伦）在 `src/` 内的第一个落点
--
-- ## 背景与定位（人类 2026-10-21 诊断的响应）
--
-- 人类诊断：「高阶同伦（`π₂ᵈ` 以上）只有定义层，没有实质计算；`Ωⁿ` 卡 K 墙」。
--
-- **本模块的实际发现（更精确的表述）**：`Ω²`/`π₂ᵈ` 的实质工作**并不缺**，
-- 但它全部位于 **`probes/`**（`_PPI5d` 定义层、`_PPI5f` `Ω3Walk`、`_PPI5g` 扩展生成集、
-- `_PPI5j` 商面、`_PEH0`–`_PEH20` 各族），**一件都没进 `src/`** ⇒ 在库内完全不可引用。
--
-- ⇒ 准确的缺口是：**「库内空白」而不是「工作空白」**。本模块把定义层提升进来。
--
-- ## 内容（复用优先：定义逐字取自 `_PPI5d:38-57`）
--
-- | 项 | 内容 |
-- |---|---|
-- | `Ω1ᵈ` | 基点闭走空间 = `Walk G x x`（定义相等，零新件）|
-- | `Ω2Walk` | **2-走** = `ASTep` 链（2-腔的组合形；索引 `w1 w2` 为**一般变量** ✓ K 安全）|
-- | `Ω2ᵈ` | 常值基点处的闭 2-走 `Ω2Walk G x (nil x) (nil x)` |
-- | `_++2_` / `++2-nilR` / `++2-assoc` | 2-走的拼接与幺半群律 ✓ |
-- | **`len2`** | **K 墙测试件**：2-走的步数，定义在**一般索引**上 ⇒ 不需要 split ✓ |
--
-- ## ★ 为什么 `len2` 是「K 墙破法」的实测件
--
-- `Ω2ᵈ G x = Ω2Walk G x (nil x) (nil x)` 的两个索引是**同一个项** `nil x`
-- ⇒ 对 `c : Ω2ᵈ G x` 做构造子 split 会撞 K 墙（`nil x = nil x` 反射方程不可消去）。
-- **破法 A**：把函数定义在**一般索引** `{w1 w2 : Walk G x x}` 上 ⇒ split 合法 ✓，
-- `Ω2ᵈ` 元素只是它的特例，**全程不需要 split** ✓
-- （与 `docs/techniques/without-k-higher-omega.md` 的破法 A 一致。）
--
-- ## ⚠ 本模块**不**包含（如实标注）
--
--   · `Ω3Walk`（3-腔关系）—— 仍在探针；
--   · 商 `π₂ᵈ = Ω2Walk / Ω3Walk` —— 需要 Cubical 的 `_/_`（探针用 `--cubical`），
--     本模块只做**定义层**，不碰商；
--   · **任何计算**（`π₂ᵈ` 的群结构 / 非平凡实例）—— 未做。
--
-- ## 核心原则
--   · 0 postulate / 0 hole
--   · 定义逐字取自探针（不重新发明）；律证明是新写的结构归纳

module Sovereign.Synthesis.Homotopy.Omega2 where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; _++w_; AStep)
open DiGraph using (V; edge)

--------------------------------------------------------------------------------
-- §1. `Ω¹ᵈ`：基点闭走空间（定义相等，零新件）
--------------------------------------------------------------------------------

Ω1ᵈ : (G : DiGraph) → V G → Set
Ω1ᵈ G x = Walk G x x

--------------------------------------------------------------------------------
-- §2. `Ω2Walk`：2-走 = `ASTep` 链
--
-- ⚠ 索引 `w1 w2` 是**一般变量**（不是同一个 `w`）—— 这是探针作者刻意的 K 安全设计，
--   也是本模块能用破法 A 的根本原因。
--------------------------------------------------------------------------------

data Ω2Walk (G : DiGraph) (x : V G) : Walk G x x → Walk G x x → Set where
  nil2  : ∀ (w : Walk G x x) → Ω2Walk G x w w
  cons2 : ∀ {w1 w2 w3 : Walk G x x}
        → AStep G w1 w2 → Ω2Walk G x w2 w3 → Ω2Walk G x w1 w3

-- `Ω²ᵈ`：常值基点处的闭 2-走
Ω2ᵈ : (G : DiGraph) → V G → Set
Ω2ᵈ G x = Ω2Walk G x (nil x) (nil x)

--------------------------------------------------------------------------------
-- §3. 拼接与幺半群律（结构归纳，全部在一般索引上 ⇒ K 安全）
--------------------------------------------------------------------------------

infixr 5 _++2_

_++2_ : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 : Walk G x x}
      → Ω2Walk G x w1 w2 → Ω2Walk G x w2 w3 → Ω2Walk G x w1 w3
nil2 _      ++2 c' = c'
cons2 s c   ++2 c' = cons2 s (c ++2 c')

++2-nilR : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
           (c : Ω2Walk G x w1 w2) → c ++2 nil2 _ ≡ c
++2-nilR (nil2 _)    = refl
++2-nilR (cons2 s c) = cong (cons2 s) (++2-nilR c)

++2-assoc : ∀ {G : DiGraph} {x : V G} {w1 w2 w3 w4 : Walk G x x}
            (c1 : Ω2Walk G x w1 w2) (c2 : Ω2Walk G x w2 w3) (c3 : Ω2Walk G x w3 w4)
          → (c1 ++2 c2) ++2 c3 ≡ c1 ++2 (c2 ++2 c3)
++2-assoc (nil2 _)    c2 c3 = refl
++2-assoc (cons2 s c) c2 c3 = cong (cons2 s) (++2-assoc c c2 c3)

--------------------------------------------------------------------------------
-- §4. ★ K 墙测试件：`len2` 定义在**一般索引**上
--
-- 对 `c : Ω2ᵈ G x` 直接归纳会撞墙（索引同为 `nil x`）；
-- 定义在 `{w1 w2}` 上则合法，`Ω2ᵈ` 元素是特例 ⇒ 全程不需要 split ✓
--------------------------------------------------------------------------------

len2 : ∀ {G : DiGraph} {x : V G} {w1 w2 : Walk G x x}
     → Ω2Walk G x w1 w2 → ℕ
len2 (nil2 _)    = zero
len2 (cons2 _ c) = suc (len2 c)

-- 特例：`Ω2ᵈ` 的元素可直接喂进 `len2`，无需消去 ✓
len2-at-Ω2ᵈ : ∀ {G : DiGraph} {x : V G} → Ω2ᵈ G x → ℕ
len2-at-Ω2ᵈ = len2
