{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyNorm
--
-- **栈式单遍归约**：去掉 `fuel`，让归约成为**真正的函数**
--
-- ## 为什么要改
--
-- `T6CayleyCode.creduce` 带 `fuel` 参数，原因是普通结构递归在 `with` 内调用
-- 通不过终止检查（实测 `TerminationIssue`：`with` 抽象后原参数成 stuck 项）。
-- 带 `fuel` 的代价：它不是「`CWalk n` 的范式」，而是「`k` 步之内的范式」
-- ⇒ 任何关于它的定理都得多带一个参数。
--
-- **栈式（累加器）写法**消除这个代价：把已处理部分压在栈 `acc` 上。
-- 关键是**在 LHS 直接匹配 `acc`**（而不是 `with acc`）——
-- 这样 `with` 只抽象「决策」，不会抽象掉递归的候选参数 `xs` ✓
-- ⇒ **普通结构递归即可通过终止检查** ✓，不需要 `fuel`。
--
-- ```
--   cpassA acc       []         = reverse acc
--   cpassA []        (x ∷ xs)   = cpassA (x ∷ []) xs
--   cpassA (y ∷ acc') (x ∷ xs)  = 若 x 与 y 互逆 ⇒ cpassA acc' xs
--                                 否则           ⇒ cpassA (x ∷ y ∷ acc') xs
-- ```
-- 复杂度：每读一个元素最多一次比较（均摊）✓
--
-- ## ⚠ 本模块**只证**「这两个函数是什么」
--
-- 不证明它们是**范式**、也不证**范式唯一**（见 §3 的如实标注）。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyCode` 的 `CStep`/`CWalk`/`cstep-inv`/`DecEq-CStep`（不重写）

module Sovereign.Synthesis.Homotopy.T6CayleyNorm where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; reverse; [_])
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)

open import Sovereign.Synthesis.Homotopy.Pi2dParity using (false≢true)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode
  using (CStep; CWalk; cplus; cminus; cstep-inv; DecEq-CStep)

--------------------------------------------------------------------------------
-- §1. ★ 栈式单遍归约（**结构递归**，无 `fuel`）
--
-- 终止性：三个递归调用的第二参数分别是 `xs`（两次）与 `xs`，
-- 都是 `x ∷ xs` 的**结构子项** ⇒ 检查器只需看第二参数 ✓
--------------------------------------------------------------------------------

cpassA : ∀ {n : ℕ} (acc xs : CWalk n) → CWalk n
cpassA acc       []           = reverse acc
cpassA []        (x ∷ xs)     = cpassA (x ∷ []) xs
cpassA (y ∷ acc') (x ∷ xs) with DecEq-CStep x (cstep-inv y)
... | yes _ = cpassA acc' xs
... | no  _ = cpassA (x ∷ y ∷ acc') xs

-- 归约：空栈启动
creduceA : ∀ {n : ℕ} (w : CWalk n) → CWalk n
creduceA = cpassA []

--------------------------------------------------------------------------------
-- §2. 两个定义性事实（`refl` 级，用来确认实现确实按预期展开）
--------------------------------------------------------------------------------

creduceA-nil : ∀ {n : ℕ} → creduceA {n} [] ≡ []
creduceA-nil = refl

creduceA-single : ∀ {n : ℕ} (x : CStep n) → creduceA [ x ] ≡ [ x ]
creduceA-single x = refl

--------------------------------------------------------------------------------
-- §3. ★★ 消去律：栈顶互逆的一对**确实被消掉**
--
-- 关键：`cstep-inv` **定义性**地对合（两构造子直接计算）
-- ⇒ `DecEq-CStep y (cstep-inv (cstep-inv y))` 就是 `DecEq-CStep y y`，
--   于是 `yes` 分支**定义性**地给出目标，`no` 分支被 `¬p refl` 排空 ✓
--   （**不需要**「判定器在自反处返回 `yes refl`」这条更强的性质。）
--------------------------------------------------------------------------------

creduceA-cancel : ∀ {n : ℕ} (y : CStep n) (xs : CWalk n)
                → creduceA (cstep-inv y ∷ y ∷ xs) ≡ creduceA xs
-- ⚠ 必须先按构造子分情形：`cstep-inv` 对**变量**卡住（无法归约），
--   只有对构造子应用才归约出 `cstep-inv (cstep-inv y) = y` ✓
creduceA-cancel (cplus j) xs with DecEq-CStep (cplus j) (cplus j)
... | yes _ = refl
... | no  ¬p = ⊥-elim (¬p refl)
creduceA-cancel (cminus j) xs with DecEq-CStep (cminus j) (cminus j)
... | yes _ = refl
... | no  ¬p = ⊥-elim (¬p refl)

--------------------------------------------------------------------------------
-- §4. ★★★ 范式性（①）：输出不含相邻可消对
--
-- ## 为什么另起一个 `cpassS`（返回**栈序**）
--
-- `cpassA` 在结束时做 `reverse`，而 `reverse` 会翻转「相邻」关系 ⇒
-- 直接在 `cpassA` 上陈述不变式要多证一条 `NoCancel-reverse`（需要
-- 「相邻关系对称」，而对称性要做 2-case 分析才能让 `cstep-inv` 归约）。
--
-- `cpassS` **不做末尾的 reverse**（直接返回栈）⇒ 不变式可直接陈述 ✓
-- 而它与 `cpassA` 的关系是 **`refl` 级**（见 §4.2）—— 代价几乎为零。
--
-- ⚠ **陈述的精确形态**：`NoCancel (creduceS w)`，其中 `creduceS w = cpassS [] w`
--   的**栈序**是「阅读顺序的逆」。**未证**：阅读顺序下的版本
--   `NoCancel (reverse (creduceS w))`（需 `NoCancel-reverse`）。
--   ⚠ 实测：`NoCancel-reverse` 比预期难 —— `reverse` 与 `nc-two` 的**头序相反**，
--     需要把消去判据沿 `reverse` 逐位搬（且每步都要 `adj-sym'`）。
--     **本模块未做**；已备 `adj-sym` / `adj-sym'` 作为它的前提。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §4.1 栈序版本
--------------------------------------------------------------------------------

cpassS : ∀ {n : ℕ} (acc xs : CWalk n) → CWalk n
cpassS acc       []           = acc
cpassS []        (x ∷ xs)     = cpassS (x ∷ []) xs
cpassS (y ∷ acc') (x ∷ xs) with DecEq-CStep x (cstep-inv y)
... | yes _ = cpassS acc' xs
... | no  _ = cpassS (x ∷ y ∷ acc') xs

creduceS : ∀ {n : ℕ} (w : CWalk n) → CWalk n
creduceS = cpassS []

--------------------------------------------------------------------------------
-- §4.2 `cpassA` 与 `cpassS` 的关系：**`refl` 级**（只差末尾一个 reverse）
--------------------------------------------------------------------------------

cpassA-eq : ∀ {n : ℕ} (acc xs : CWalk n)
          → cpassA acc xs ≡ reverse (cpassS acc xs)
cpassA-eq acc       []      = refl
cpassA-eq []        (x ∷ xs) = cpassA-eq (x ∷ []) xs
cpassA-eq (y ∷ acc') (x ∷ xs) with DecEq-CStep x (cstep-inv y)
... | yes _ = cpassA-eq acc' xs
... | no  _ = cpassA-eq (x ∷ y ∷ acc') xs

--------------------------------------------------------------------------------
-- §4.3 ★★ 不变式：`NoCancel`
--------------------------------------------------------------------------------

data NoCancel {n : ℕ} : CWalk n → Set where
  nc-nil  : NoCancel []
  nc-one  : (x : CStep n) → NoCancel (x ∷ [])
  nc-two  : (x y : CStep n) (xs : CWalk n)
          → ¬ (x ≡ cstep-inv y) → NoCancel (y ∷ xs) → NoCancel (x ∷ y ∷ xs)

-- 取尾（`nc-two` 的尾；`nc-one` 的尾是空栈）
NoCancel-tail : ∀ {n : ℕ} (y : CStep n) (acc' : CWalk n)
              → NoCancel (y ∷ acc') → NoCancel acc'
NoCancel-tail y []       (nc-one .y)        = nc-nil
NoCancel-tail y (z ∷ zs) (nc-two .y z zs _ t) = t

--------------------------------------------------------------------------------
-- §4.4 ★★★ 主定理：栈式归约保持「无可消对」
--------------------------------------------------------------------------------

cpassS-noCancel : ∀ {n : ℕ} (acc xs : CWalk n)
                → NoCancel acc → NoCancel (cpassS acc xs)
cpassS-noCancel acc       []           h = h
cpassS-noCancel []        (x ∷ xs)     _ = cpassS-noCancel (x ∷ []) xs (nc-one x)
cpassS-noCancel (y ∷ acc') (x ∷ xs)   h with DecEq-CStep x (cstep-inv y)
... | yes _ = cpassS-noCancel acc' xs (NoCancel-tail y acc' h)
... | no  ¬p = cpassS-noCancel (x ∷ y ∷ acc') xs (nc-two x y acc' ¬p h)

-- ★★ ① 范式性：归约结果（栈序）不含相邻可消对
creduceS-noCancel : ∀ {n : ℕ} (w : CWalk n) → NoCancel (creduceS w)
creduceS-noCancel w = cpassS-noCancel [] w nc-nil

--------------------------------------------------------------------------------
-- §4.5 ★★ 相邻关系对称（`cstep-inv` 对合 ⇒ 可翻转）
--
-- 用途：`NoCancel` 在 `reverse` 下不变、以及 `creduceA` 幂等，**都**以它为共同前提。
-- ⚠ 必须**按 `x` 的构造子分情形** —— 变量上 `cstep-inv (cstep-inv x)` 卡住。
--------------------------------------------------------------------------------

-- 两个投影：取索引与取方向（用来从「构造子相等」里提取信息 / 区分方向）
cfin : ∀ {n : ℕ} → CStep n → Fin n
cfin (cplus j)  = j
cfin (cminus j) = j

cdir : ∀ {n : ℕ} → CStep n → Bool
cdir (cplus _)  = true
cdir (cminus _) = false

adj-sym : ∀ {n : ℕ} (x y : CStep n)
        → x ≡ cstep-inv y → y ≡ cstep-inv x
adj-sym (cplus j)  (cplus k)  e = ⊥-elim (false≢true (sym (cong cdir e)))
adj-sym (cplus j)  (cminus k) e = sym (cong cminus (cong cfin e))
adj-sym (cminus j) (cplus k)  e = sym (cong cplus (cong cfin e))
adj-sym (cminus j) (cminus k) e = ⊥-elim (false≢true (cong cdir e))

adj-sym' : ∀ {n : ℕ} (x y : CStep n)
         → ¬ (x ≡ cstep-inv y) → ¬ (y ≡ cstep-inv x)
adj-sym' x y ¬p q = ¬p (adj-sym y x q)

--------------------------------------------------------------------------------
-- §4.6 ★★ 阅读序谓词 `NoCancelR` 与 `NoCancel` 的**双向桥**
--
-- 两个谓词形状相同，只差**相邻对的书写次序**：
--
-- | 谓词 | 相邻对条件 | 读法 |
-- |---|---|---|
-- | `NoCancel`  | `¬ (x ≡ cstep-inv y)` | `x` 比 `y` **新**（栈序）|
-- | `NoCancelR` | `¬ (y ≡ cstep-inv x)` | `x` 比 `y` **旧**（阅读序）|
--
-- ⇒ 桥就是 **`adj-sym'`**（相邻关系对称）✓ —— `§4.5` 已经证好了。
--------------------------------------------------------------------------------

data NoCancelR {n : ℕ} : CWalk n → Set where
  nr-nil  : NoCancelR []
  nr-one  : (x : CStep n) → NoCancelR (x ∷ [])
  nr-two  : (x y : CStep n) (xs : CWalk n)
          → ¬ (y ≡ cstep-inv x) → NoCancelR (y ∷ xs) → NoCancelR (x ∷ y ∷ xs)

-- ★ 栈序 ⇒ 阅读序
NoCancel→R : ∀ {n : ℕ} {w : CWalk n} → NoCancel w → NoCancelR w
NoCancel→R nc-nil                  = nr-nil
NoCancel→R (nc-one x)              = nr-one x
NoCancel→R (nc-two x y xs ¬p t)    = nr-two x y xs (adj-sym' x y ¬p) (NoCancel→R t)

-- ★ 阅读序 ⇒ 栈序（反方向，同样只用 `adj-sym'`）
R→NoCancel : ∀ {n : ℕ} {w : CWalk n} → NoCancelR w → NoCancel w
R→NoCancel nr-nil                = nc-nil
R→NoCancel (nr-one x)            = nc-one x
R→NoCancel (nr-two x y xs ¬q t)  = nc-two x y xs (adj-sym' y x ¬q) (R→NoCancel t)

-- ★★ 主定理的**阅读序**版本（同一件事的两种写法）
creduceS-noCancelR : ∀ {n : ℕ} (w : CWalk n) → NoCancelR (creduceS w)
creduceS-noCancelR w = NoCancel→R (creduceS-noCancel w)

--------------------------------------------------------------------------------
-- §5. ⚠ 本模块**不**声称的（如实标注；这些都不是「顺手就能做」）
--
-- ① **消去律** —— ✅ **已证（见 §3 `creduceA-cancel`）**
-- ② **范式性**：`creduceA` 的输出不含相邻逆对。**未证**。
-- ③ **幂等 / 范式唯一**。**未证**。
-- ④ **语义正确**：`creduceA` 不改变 `foldT`（`T6CayleyCodeWalk`）的终点。**未证**。
--
-- ⇒ 本模块的成立事实只有：`cpassA`/`creduceA` **存在、终止、按上述模式展开**
--   （外加 §2 两条 `refl`）。**不**包含任何「它是范式」的断言。
--------------------------------------------------------------------------------
