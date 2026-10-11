{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Automata.DFA
-- 确定有限自动机（DFA）——离散数学基础任务池 P2 末件
--
-- 数学背景：DFA = (Q, Σ, δ, q₀, F) 五元组（Hopcroft-Ullman 经典形）：
--   有限状态集 Q、字母表 Σ、转移函数 δ : Q → Σ → Q（确定性=函数形，
--   关系入定义原则下转移是**函数字段**非关系公理）、初态 q₀、接受集 F。
--   语言 = 被 run 逐步送入 δ 后落在 F 的词集。
--
-- 核心原则：
-- 1. 关系入定义：DFA record 承载全部五元组分量——无外来公理；
--    转移的确定性由**函数类型** δ : Q → Σ → Q 自证（非确定形 NFA 立界）。
-- 2. 运行语义 run 为 List 归纳（词=字母表列表）——执行面与语言面分离。
-- 3. 核对层用数据形 refl（Bool 通道 + Fin 2 构造子形）。
-- 4. Myhill-Nerode 为深件——立界注记不硬拱（任务池诚实边界）。
--
-- 包含：DFA record · run · accepts · Lang · mod2（模 2 奇偶识别器）
--       · acceptAll（单态全收）· 核对层 · Myhill-Nerode 立界

module Sovereign.Algebra.Automata.DFA where

open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ────────────────────────────────────────────────────────────────────
-- §1 DFA 定义层（五元组 record——关系入定义：确定性由 δ 函数形承载）
-- ────────────────────────────────────────────────────────────────────

record DFA (Q Σ : Set) : Set where
  field
    δ     : Q → Σ → Q        -- 转移（确定性=函数；NFA 关系形立界）
    q₀    : Q                -- 初态
    accept : Q → Bool        -- 接受判据（F 的谓词形，Bool 通道免 Dec 面）

-- ────────────────────────────────────────────────────────────────────
-- §2 运行语义（run）与语言面（accepts / Lang）
-- ────────────────────────────────────────────────────────────────────

-- run：词上的状态演化（List 归纳——空词停初态）
run : {Q Σ : Set} → DFA Q Σ → List Σ → Q
run M []       = DFA.q₀ M
run M (a ∷ w)  = DFA.δ M (run M w) a

-- accepts：词的接受判定（Bool 通道）
accepts : {Q Σ : Set} → DFA Q Σ → List Σ → Bool
accepts M w = DFA.accept M (run M w)

-- Lang：接受语言（关系形定义——词被接受的命题）
Lang : {Q Σ : Set} → DFA Q Σ → List Σ → Set
Lang M w = accepts M w ≡ true

-- ────────────────────────────────────────────────────────────────────
-- §3 实例一：mod2——二态模 2 奇偶识别器（接受偶长词）
--   Q = Fin 2（fzero=偶/fsuc fzero=奇）；Σ = ⊤（每符号计 1）；
--   δ = 翻转；F = {偶}。经典 2 状态模 2 识别器。
-- ────────────────────────────────────────────────────────────────────

mod2-δ : Fin 2 → ⊤ → Fin 2
mod2-δ fzero       _ = fsuc fzero
mod2-δ (fsuc fzero) _ = fzero

mod2 : DFA (Fin 2) ⊤
mod2 = record
  { δ      = mod2-δ
  ; q₀     = fzero
  ; accept = λ { fzero → true ; (fsuc fzero) → false }
  }

-- 核对层（mod2）：空词/单符号/双符号——数据形 refl（Bool 通道）
check-mod2-empty : Lang mod2 []
check-mod2-empty = refl

check-mod2-one : accepts mod2 (tt ∷ []) ≡ false
check-mod2-one = refl

check-mod2-two : Lang mod2 (tt ∷ tt ∷ [])
check-mod2-two = refl

check-mod2-three : accepts mod2 (tt ∷ tt ∷ tt ∷ []) ≡ false
check-mod2-three = refl

-- ────────────────────────────────────────────────────────────────────
-- §4 实例二：acceptAll——单态全收机（Q = ⊤，一切词入语言）
-- ────────────────────────────────────────────────────────────────────

acceptAll : DFA ⊤ ⊤
acceptAll = record
  { δ      = λ _ _ → tt
  ; q₀     = tt
  ; accept = λ _ → true
  }

check-all-three : Lang acceptAll (tt ∷ tt ∷ tt ∷ [])
check-all-three = refl

check-all-run : run acceptAll (tt ∷ tt ∷ []) ≡ tt
check-all-run = refl

-- ────────────────────────────────────────────────────────────────────
-- §5 立界注记（诚实边界——不设空壳签名）
-- (i)   NFA 形（δ : Q → Σ → List Q）与子集构造——后续批；
-- (ii)  正则语言封闭性（并/交/补/连接/星）——需 NFA 或正则表达式面；
-- (iii) **Myhill-Nerode 定理**（语言正则 ⟺ 有限指数等价类）——深件：
--       需等价类商 + 有限性判据双向，估 200-300 行独立批，不硬拱；
-- (iv)  泵引理（正则语言泵性质）——深件同族。
-- ────────────────────────────────────────────────────────────────────
