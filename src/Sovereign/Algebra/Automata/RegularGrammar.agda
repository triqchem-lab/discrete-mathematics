{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Automata.RegularGrammar
-- 正则文法（右线性）与生成语言——DFA 面的文法侧衔接件
-- 数学背景：右线性文法 = 产生式形 n → w（终止）或 n → w·n'（延续），
--   w 为终符串。生成语义 = 归纳型（gen-done/gen-step 两规则）。
--   Kleene 定理（正则文法 ⟺ 正则语言 ⟺ DFA 可识别）为深件——立界注记。
--
-- 核心原则：
-- 1. 产生式表即结构（关系入定义：record 字段 = 文法全部内容，零外来公理）
-- 2. 生成语义归纳型承载（数据形两规则 = 文法推导）
-- 3. 0 postulate / 0 hole；穷举边界遵守
--
-- 包含：∈L · RegGrammar · Generates · egS 实例 · 核对层

module Sovereign.Algebra.Automata.RegularGrammar where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infix 4 _∈L_

-- §1 成员关系（自含——免 membership 导入面）
data _∈L_ {A : Set} : A → List A → Set where
  hd : ∀ {x xs} → x ∈L (x ∷ xs)
  tl : ∀ {x y xs} → x ∈L xs → x ∈L (y ∷ xs)

-- §2 右线性文法（产生式表即结构——presentation 最小性自检：无导出字段）
record RegGrammar (N T : Set) : Set where
  field
    start : N
    prod  : N → List (List T × Maybe N)

-- §3 生成语义（归纳型两规则：终止产生式 / 延续产生式）
data Generates {N T : Set} (prod : N → List (List T × Maybe N)) : N → List T → Set where
  gen-done : ∀ {n w}
           → (w , nothing) ∈L prod n
           → Generates prod n w
  gen-step : ∀ {n m w v}
           → (w , just m) ∈L prod n
           → Generates prod m v
           → Generates prod n (w ++ v)

-- §4 实例：单非终 S、单符号 a——S → ε | a·S（L = a*）
egS : RegGrammar ⊤ ⊤
egS = record
  { start = tt
  ; prod  = λ _ → ([] , nothing) ∷ ((tt ∷ []) , just tt) ∷ []
  }

egProd : ⊤ → List (List ⊤ × Maybe ⊤)
egProd = RegGrammar.prod egS

-- §5 核对层（inhabitation 三案——空词/单符号/双符号）
check-gen-ε : Generates egProd tt []
check-gen-ε = gen-done hd

check-gen-a : Generates egProd tt (tt ∷ [])
check-gen-a = gen-step (tl hd) (gen-done hd)

check-gen-aa : Generates egProd tt (tt ∷ tt ∷ [])
check-gen-aa = gen-step (tl hd) (gen-step (tl hd) (gen-done hd))

-- 立界注记（§6）：Kleene 定理（正则文法 ⟺ DFA 可识别——深件 200-300 行）
-- ／一般正则文法（含左线性/混线性）／语言类封闭性——不设空壳签名。
