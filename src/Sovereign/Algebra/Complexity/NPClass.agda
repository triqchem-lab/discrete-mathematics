{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.NPClass
-- NP 类——非确定性多项式时间语言的验证器范式（W1 计算模型层第 3 件，路径乙）
--
-- 数学背景：经典 NP = 「存在多项式长见证 + 多项式时间验证器的语言」。
-- 本件在带计账函数层（TimeBound.Counted）给验证器范式：
--
--   L ∈ NP ⟺ ∃ 多项式界 p（单调 + 正）
--            + 见证长度界 w（单调 + 正；见证集 = Vec Trit (w n)）
--            + 验证器 V : ∀ n x → Vec Trit (w n) → Counted Bool
--            + 完备性：L n x → ∃ 见证 w′，V n x w′ 接受        〔结构证明〕
--            + 正确性：V n x w′ 接受 → L n x（对一切见证）     〔结构证明〕
--            + 代价界：V 的账目 ≤ p n（对一切见证）             〔结构证明〕
--
-- 与 P 的关系：P ⊆ NP 本件闭合（§3，见证长度取 0、验证器忽略见证）；
-- NP ⊆ P（P = NP）是开放问题，本库不设任何形式的「分离」断言（诚实纪律：
-- L15 自警「非 Agda 工程可解」，分离主张一律立界不冒充）。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.NPClass where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤n⇒m≤1+n)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

-- 引用边界（跨域引用注记）：
--   Sovereign.Base.Trit —— 仅取载体类型与构造子（同 PClass 纪律）；
--   Sovereign.Algebra.Complexity.TimeBound —— 计账基元（同层，无跨域）；
--   Sovereign.Algebra.Complexity.PClass —— P 类 record（同层，P⊆NP 桥）。
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Complexity.TimeBound
  using (Counted; value; steps; StepsLE; Mono; Pos;
         polySuc; polySuc-mono; polySuc-pos)
  renaming (cnt to mkCnt)
open import Sovereign.Algebra.Complexity.PClass
  using (TritLang; Decider; InP; headT; L-Head₁; dec-Head₁; head-P)

-- ────────────────────────────────────────────────────────────────────
-- §1 NP 类 record〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

record InNP (L : TritLang) : Set₁ where
  field
    np-p        : ℕ → ℕ              -- 代价多项式界
    np-p-mono   : Mono np-p          -- 〔结构证明〕
    np-p-pos    : Pos np-p           -- 〔结构证明〕
    np-witLen   : ℕ → ℕ              -- 见证长度界（以位数 n 为规模）
    np-w-mono   : Mono np-witLen     -- 〔结构证明〕
    np-verifier : (n : ℕ) → Vec Trit n → Vec Trit (np-witLen n) → Counted Bool
    np-complete : ∀ n x → L n x →
      Σ (Vec Trit (np-witLen n)) (λ w → value (np-verifier n x w) ≡ true)
    np-sound    : ∀ n x w → value (np-verifier n x w) ≡ true → L n x
    np-cost     : ∀ n x w → steps (np-verifier n x w) ≤ np-p n

-- ────────────────────────────────────────────────────────────────────
-- §2 界放大封闭〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 代价界放大（见证集不动——完全闭合）
inNP-rebound-p : ∀ {L} (dp : InNP L) (q : ℕ → ℕ)
               → Mono q → Pos q → (∀ n → InNP.np-p dp n ≤ q n) → InNP L
inNP-rebound-p dp q q-mono q-pos h =
  record { np-p = q ; np-p-mono = q-mono ; np-p-pos = q-pos
         ; np-witLen = InNP.np-witLen dp ; np-w-mono = InNP.np-w-mono dp
         ; np-verifier = InNP.np-verifier dp
         ; np-complete = InNP.np-complete dp
         ; np-sound = InNP.np-sound dp
         ; np-cost = λ n x w → ≤-trans (InNP.np-cost dp n x w) (h n) }

-- ────────────────────────────────────────────────────────────────────
-- §3 P ⊆ NP〔结构证明——W1 三件套的核心连接〕
-- ────────────────────────────────────────────────────────────────────

-- 见证长度取 0（Vec Trit 0 仅 []），验证器忽略见证 = P 判定器。
-- 完备性：见证取 []；正确性/代价界逐字继承 InP。
inP⇒inNP : ∀ {L} (dp : InP L) → InNP L
inP⇒inNP dp = record
  { np-p = InP.p dp
  ; np-p-mono = InP.p-mono dp
  ; np-p-pos = InP.p-pos dp
  ; np-witLen = λ _ → 0
  ; np-w-mono = λ _ → z≤n
  ; np-verifier = λ n x _ → InP.decider dp n x
  ; np-complete = λ n x l → [] , InP.p-complete dp n x l
  ; np-sound = λ n x w v → InP.p-sound dp n x v
  ; np-cost = λ n x w → InP.p-cost dp n x }

-- 推论：首位检测语言 ∈ NP
head-NP : InNP L-Head₁
head-NP = inP⇒inNP head-P

-- ────────────────────────────────────────────────────────────────────
-- §4 核对层（空语言玩具例 + P⊆NP 的域核对）〔refl 枚举 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 空语言（⊥）：NP 成员性空洞成立（验证器恒拒绝）
L-Bot : TritLang
L-Bot n x = ⊥

bot-NP : InNP L-Bot
bot-NP = record
  { np-p = polySuc ; np-p-mono = polySuc-mono ; np-p-pos = polySuc-pos
  ; np-witLen = λ _ → 1
  ; np-w-mono = λ _ → s≤s z≤n
  ; np-verifier = λ n x w → mkCnt false 0
  ; np-complete = λ n x l → ⊥-elim l
  ; np-sound = λ n x w ()
  ; np-cost = λ n x w → z≤n }

-- head-NP 的验证器 = 忽略见证的 head 判定器（域核对）
check-head-NP : value (InNP.np-verifier head-NP 2 (T₁ ∷ T₀ ∷ []) []) ≡ true
check-head-NP = refl

-- 见证长度界确为 0（np-witLen head-NP n = 0，vec 类型无第三实参可写，
-- 以 complete 的见证集类型核对）
check-witlen : ∀ n → InNP.np-witLen head-NP n ≡ 0
check-witlen n = refl

-- ────────────────────────────────────────────────────────────────────
-- §5 立界注记
-- ────────────────────────────────────────────────────────────────────
-- (i)   NP ⊆ P / P ≠ NP——开放问题，本库永不设断言（分离主张 =
--       「非线性下界 + 对角化」世界级深件，L15 纪律：立界不冒充）。
-- (ii)  inNP-rebound 的**见证集放大**（长 wq n 见证截断为 witLen n）需
--       Vec 截断/重填 API，忠实 cast 独立小件；代价放大版已闭合。
-- (iii) 「验证器可由 TM 实现」：通用形式同 PClass §6(i) 桥立界（本 record
--       不断言）；SAT 验证器（含族池 w(n) 形）的实例桥已由 SATMBridge 闭合。
-- (iv)  NP 完备性：归约族侧已落地（SATRed：归约框架 Reduces + NP 对归约
--       封闭 red-preserves-NP + 真归约实例）；Cook-Levin 型**NP-难**仍立界
--       （任意验证器 → CNF 的 tableau 编码，W2）。

-- 0 postulate / 0 hole。
