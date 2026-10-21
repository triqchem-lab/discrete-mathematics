{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyCode
--
-- **码层归约** —— 路 (a4)：把 `reduce` 搬到**无证明分量**的表示上
--
-- ## 为什么需要码层（第三次修正后的正确形状）
--
-- 台账边界 `PN.B4.pi2d-free-group-boundary` 记了三次修正。前三次的共同错误是：
-- **想在「含见证的对象」上做判定**：
--
-- | 版本 | 形状 | 为何不行 |
-- |---|---|---|
-- | (a) | `DecEq (ASTep G _ _)` | `ASTep` 含 edge 见证 ⇒ 需 uip |
-- | (a1) | 边编码 `code : edge x y → Fin n` | 仍要比较**见证** ⇒ 需 uip |
-- | (a3) | `Dec (y ≡ updAt j x)`（语句层） | ✅ 无 uip，但只判**存在性** —— 归约要的是「这两步是同一条边的正反吗」，那要**见证的同一性** ✗ |
--
-- **⇒ 正确形状 (a4)：把归约完全搬到「码」层。**
--
-- ```
--   data CStep : cplus j  /  cminus j          （方向 + 坐标，**无证明分量**）
--   CWalk = List CStep                          （相等**可判定**，平凡）
--   creduce : fuel → CWalk → CWalk               （在码上做，**完全可计算**）
-- ```
-- 归约在码层（无 uip）；见证只在**翻译边界**（`CWalk → Walk …`）出现一次。
--
-- ## 本模块交付（码层，全部可判定/可计算）
--
-- | 项 | 内容 |
-- |---|---|
-- | `CStep` / `CWalk` | 步的码 / 走的码 |
-- | `cstep-inv` | 码的逆（`cplus j ↔ cminus j`）—— 对合 |
-- | `DecEq-CStep` / `DecEq-CWalk` | 码的**可判定相等**（平凡，无需 uip）|
-- | `cpass` | 一遍消去（相邻逆对）|
-- | `creduce` | `fuel` 遍消去 |
--
-- ## ⚠ 本模块**不**包含
--
--   · 翻译边界 `CWalk → Walk …`（见证只在那里出现）—— 下一步；
--   · `creduce` 与 `Ω3Walk⁺` 的对应（分类定理本体）—— 再下一步。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · `cpass` 的终止性靠**结构递归**（两个分支都严格变小），不需要 WF

module Sovereign.Synthesis.Homotopy.T6CayleyCode where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

--------------------------------------------------------------------------------
-- §1. 码：方向 + 坐标（**无证明分量**）
--------------------------------------------------------------------------------

data CStep (n : ℕ) : Set where
  cplus  : Fin n → CStep n      -- 沿 `+e_j`
  cminus : Fin n → CStep n      -- 沿 `−e_j`

CWalk : ℕ → Set
CWalk n = List (CStep n)

-- 码的逆（对合）
cstep-inv : ∀ {n : ℕ} → CStep n → CStep n
cstep-inv (cplus j)  = cminus j
cstep-inv (cminus j) = cplus j

cstep-inv-invol : ∀ {n : ℕ} (s : CStep n) → cstep-inv (cstep-inv s) ≡ s
cstep-inv-invol (cplus j)  = refl
cstep-inv-invol (cminus j) = refl

--------------------------------------------------------------------------------
-- §2. ★ 码的可判定相等（平凡：两个构造子 + `Fin` 的 `≟`，**完全不用 uip**）
--------------------------------------------------------------------------------

DecEq-CStep : ∀ {n : ℕ} (s s' : CStep n) → Dec (s ≡ s')
DecEq-CStep (cplus j)  (cplus j')  with j Fin.≟ j'
... | yes p = yes (cong cplus p)
... | no  ¬p = no λ { refl → ¬p refl }
DecEq-CStep (cplus j)  (cminus j') = no λ ()
DecEq-CStep (cminus j) (cplus j')  = no λ ()
DecEq-CStep (cminus j) (cminus j') with j Fin.≟ j'
... | yes p = yes (cong cminus p)
... | no  ¬p = no λ { refl → ¬p refl }

DecEq-CWalk : ∀ {n : ℕ} (w w' : CWalk n) → Dec (w ≡ w')
DecEq-CWalk []       []        = yes refl
DecEq-CWalk []       (x ∷ _)   = no λ ()
DecEq-CWalk (x ∷ _)  []        = no λ ()
DecEq-CWalk (x ∷ w)  (x' ∷ w') with DecEq-CStep x x'
... | no  ¬p = no λ { refl → ¬p refl }
... | yes p  with DecEq-CWalk w w'
...   | yes q  = yes (cong₂ _∷_ p q)
...   | no  ¬q = no λ { refl → ¬q refl }

--------------------------------------------------------------------------------
-- §3. ★★ 码层归约（`fuel` 递归）
--
-- ⚠ 为什么用 `fuel` 而不是普通结构递归：
--   普通结构递归在 `with` 内调用会**通不过终止检查** ——
--   设计算 `DecEq-CStep y (cstep-inv x)` 后，`cpass rest` 的 `rest`
--   在检查器看来不是「原参数 `x ∷ y ∷ rest` 的子项」（`with` 抽象后原参数变成 stuck 项）。
--   实测报 `TerminationIssue`。⇒ 改为按 `fuel` 结构递归（`k` 严格变小）✓
--
-- ⚠ 语义：一次 `fuel` = **一次消去**（不是一遍扫描）。
--------------------------------------------------------------------------------

creduce : ∀ {n : ℕ} (k : ℕ) (w : CWalk n) → CWalk n
creduce zero    w                = w
creduce (suc k) []               = []
creduce (suc k) (x ∷ [])         = x ∷ []
creduce (suc k) (x ∷ y ∷ rest) with DecEq-CStep y (cstep-inv x)
... | yes _ = creduce k rest
... | no  _ = x ∷ creduce k (y ∷ rest)

--------------------------------------------------------------------------------
-- §4. ⬜ 本模块**不**声称的（如实标注）
--
--   · **完备性**：上面的 `creduce` 在 `no` 分支不重查 `x` 是否与新头消去
--     ⇒ **一遍不保证到不动点**。要完备得改成「消尾后重查整条」或迭代到不动点，
--     而「迭代到不动点是否唯一」= **汇合性**（本线最硬的一段，未做）。
--   · **翻译边界**：`interpret : (n) (x : T6Vec n) → CWalk n → Σ (λ (y : T6Vec n) → Walk (T6CayleySym n) x y)`
--     —— 见证只在这一层出现一次。
--   · **与 `Ω3Walk⁺` 的对应**：`creduce` 的每步对应 `Ω3Walk⁺`（分类定理本体）。
--------------------------------------------------------------------------------
