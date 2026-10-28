{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.PClass
-- P 类——确定性多项式时间语言的 Agda 形（W1 计算模型层第 2 件，路径乙）
--
-- 数学背景：经典 P = 「存在确定性多项式时间判定器的语言」。本件把判定器取为
-- **带计账的结构递归函数**（TimeBound.Counted——函数自带步数簿记），语言取为
-- trit 串族上的谓词（本库母语：Vec Trit n，与 Base.Trit 对齐；不引入布尔串
-- 为主载体）。语言成员 x ∈ L ⟺ L n x 非空（Set 值谓词）。
--
--   InP L = ∃ 判定器 dec（总函数，Agda 类型检查保证总化）
--           + 多项式界 p（单调 + 正，TimeBound.Mono/Pos）
--           + 完备性（L n x → dec 接受）〔结构证明〕
--           + 正确性（dec 接受 → L n x）〔结构证明〕
--           + 代价界（dec 的账目 ≤ p n）〔结构证明〕
--
-- 诚实边界：「dec 实现为 TM」= 函数层 → 图灵机层的编码桥，属立界（见文尾）；
-- 本件全部内容在函数层闭合，无空壳签名。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.PClass where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

-- 引用边界（跨域引用注记）：
--   Sovereign.Base.Trit —— GF(3) 三值域；本件仅用其载体类型与三构造子，
--   不依赖 ⊕/⊗ 环结构（复杂度层与代数层正交，见 Fable 裁定「代数污染禁止」）。
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.Complexity.TimeBound
  using (Counted; value; steps; StepsLE; Mono; Pos;
         polySuc; polySuc-mono; polySuc-pos; bound-mono)
  renaming (cnt to mkCnt)

-- ────────────────────────────────────────────────────────────────────
-- §1 输入域与语言〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- trit 串族：n 位输入 = Vec Trit n（函数编码 Fin n → Trit 的 Vec 对偶形，
-- 与 GF3Count 的 (Fin d → Trit) 计数 3^d 相容——位数即维数）。
-- 语言：按位数索引的谓词族。
TritLang : Set₁
TritLang = (n : ℕ) → Vec Trit n → Set

-- 判定器：带计账的布尔值函数族（值域 Set 层）
Decider : Set
Decider = (n : ℕ) → Vec Trit n → Counted Bool

-- ────────────────────────────────────────────────────────────────────
-- §2 P 类 record〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- L ∈ P ⟺ 存在判定器 + 多项式界 + 三条可证相容性
record InP (L : TritLang) : Set₁ where
  field
    p          : ℕ → ℕ                 -- 多项式界（以位数 n 为规模）
    p-mono     : Mono p                -- 界单调〔结构证明〕
    p-pos      : Pos p                 -- 界正性〔结构证明〕
    decider    : Decider               -- 判定器（总化由 Agda 保证）
    p-complete : ∀ n x → L n x → value (decider n x) ≡ true   -- 完备性〔结构证明〕
    p-sound    : ∀ n x → value (decider n x) ≡ true → L n x   -- 正确性〔结构证明〕
    p-cost     : ∀ n x → steps (decider n x) ≤ p n            -- 代价界〔结构证明〕

-- ────────────────────────────────────────────────────────────────────
-- §3 界放大封闭（P 对更大多项式界封闭）〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 若 q 处处 ≥ p 且 q 仍单调正，则 InP 换界不破——P 的界非规范形（经典性质）
inP-rebound : ∀ {L} (dp : InP L) (q : ℕ → ℕ)
            → Mono q → Pos q → (∀ n → InP.p dp n ≤ q n) → InP L
inP-rebound dp q q-mono q-pos h =
  record { p = q ; p-mono = q-mono ; p-pos = q-pos
         ; decider = InP.decider dp
         ; p-complete = InP.p-complete dp
         ; p-sound = InP.p-sound dp
         ; p-cost = λ n x → ≤-trans (InP.p-cost dp n x) (h n) }

-- ────────────────────────────────────────────────────────────────────
-- §4 非平凡实例：首位检测（常数代价 1 步）〔结构证明 + refl 实例〕
-- ────────────────────────────────────────────────────────────────────

-- 首位提取（空串取 T₀——规范自由度）
headT : ∀ {n} → Vec Trit n → Trit
headT [] = T₀
headT (t ∷ _) = t

-- 语言：首位是 T₁
L-Head₁ : TritLang
L-Head₁ n x = headT x ≡ T₁

isT₁ : Trit → Bool
isT₁ T₀ = false
isT₁ T₁ = true
isT₁ T₂ = false

-- 判定器：读首位，1 步（常数代价——最便宜的非常凡语言）
dec-Head₁ : Decider
dec-Head₁ n x = mkCnt (isT₁ (headT x)) 1

isT₁-sound : ∀ t → isT₁ t ≡ true → t ≡ T₁
isT₁-sound T₀ ()
isT₁-sound T₁ _  = refl
isT₁-sound T₂ ()

head-P : InP L-Head₁
head-P = record
  { p = polySuc ; p-mono = polySuc-mono ; p-pos = polySuc-pos
  ; decider = dec-Head₁
  ; p-complete = λ n x h → trans (cong isT₁ h) refl
  ; p-sound = λ n x h → isT₁-sound (headT x) h
  ; p-cost = λ n x → s≤s z≤n }   -- 1 ≤ suc n

-- ────────────────────────────────────────────────────────────────────
-- §5 核对层〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

check-head-accept : value (dec-Head₁ 3 (T₁ ∷ T₂ ∷ T₀ ∷ [])) ≡ true
check-head-accept = refl

check-head-reject : value (dec-Head₁ 3 (T₂ ∷ T₁ ∷ T₀ ∷ [])) ≡ false
check-head-reject = refl

check-head-steps : steps (dec-Head₁ 1 (T₁ ∷ [])) ≡ 1
check-head-steps = refl

-- 完备性实例化（具体语言成员的完备性域展开；值由 dec-Head₁ 定义性归约）
probe-headT : headT (T₁ ∷ T₀ ∷ []) ≡ T₁
probe-headT = refl

probe-isT₁ : isT₁ (headT (T₁ ∷ T₀ ∷ [])) ≡ true
probe-isT₁ = refl

probe-value : value (mkCnt (isT₁ (headT (T₁ ∷ T₀ ∷ []))) 1) ≡ true
probe-value = refl

check-complete : value (dec-Head₁ 2 (T₁ ∷ T₀ ∷ [])) ≡ true
check-complete = refl

-- record 域可用性核对：p-complete 应用于具体成员
check-complete-domain : L-Head₁ 2 (T₁ ∷ T₀ ∷ []) →
                        value (dec-Head₁ 2 (T₁ ∷ T₀ ∷ [])) ≡ true
check-complete-domain = InP.p-complete head-P 2 (T₁ ∷ T₀ ∷ [])

-- ────────────────────────────────────────────────────────────────────
-- §6 立界注记
-- ────────────────────────────────────────────────────────────────────
-- (i)   「decider 可由 TM 实现」——函数层 → Automata.TuringMachine 的编码桥
--       （Church-Turing 型深件），故本件是 P 的**函数层形**，与经典定义的
--       对齐立界；桥闭合后 head-P 等实例自动提升为 TM 多项式语言。
-- (ii)  P 对多项式复合的封闭（dec∘dec 的界合成）——需界复合引理
--       （poly ∘ poly 仍 poly 且单调），中件，独立批。
-- (iii) 语言族的规范形：本件 TritLang 按 n 全体索引；「仅对 n ∈ S 有定义」的
--       子族语言（如 SAT 的 3c(1+m) 整除层）以 ⊥ 填充，语义诚实。

-- 0 postulate / 0 hole。
