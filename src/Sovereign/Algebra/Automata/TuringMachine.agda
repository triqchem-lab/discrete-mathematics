{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Automata.TuringMachine
-- 图灵机（TM）——离散数学基础任务池 P3 尾批（深件声明层起步）
--
-- 数学背景：图灵机 = (Q, Σ, δ, q₀, halt)（Hopcroft-Ullman 经典形）：
--   有限状态集 Q、带字母表 Σ（含空白符）、转移
--   δ : Q → Σ → Q × Σ × Dir（写符号/移向/转态）、初态 q₀、停机判据 halt。
--   格局 = (左带, 状态, 当前符号, 右带)；一步 = δ 驱动的带改写+移头。
--
-- 核心原则：
-- 1. 关系入定义：TM record 承载全部分量——确定性由 δ 函数形自证（与 DFA 同范式）；
-- 2. 执行面用**燃料形** runN（ℕ 步界）——避开停机性递归问题（Agda 良基性
--    与停机性不可判定同源：run 总化需燃料是诚实设计非缺陷）；
-- 3. 核对层数据形 refl（具体格局步进 defeq）；
-- 4. ⚠ 诚实边界：**Church-Turing 论题/停机不可判定/通用机构造 = 深件**
--    （200-400 行独立批）——立界注记，不设空壳签名。
--
-- 包含：Dir · TM record · TConfig · step · runN · 计算性声明面 · 最小实例 · 核对层

module Sovereign.Algebra.Automata.TuringMachine where

open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ────────────────────────────────────────────────────────────────────
-- §1 定义层（五元组 record——关系入定义）
-- ────────────────────────────────────────────────────────────────────

-- 移头方向
data Dir : Set where
  L : Dir
  R : Dir

record TM (Q Σ : Set) : Set where
  field
    δ    : Q → Σ → Q × Σ × Dir   -- 转移（确定性=函数形自证）
    q₀   : Q                     -- 初态
    halt : Q → Bool              -- 停机判据（Bool 通道——与 DFA accept 同范式）

-- 格局：左带（倒序存）· 状态 · 当前符号 · 右带
record TConfig (Q Σ : Set) : Set where
  constructor mkTC
  field
    left  : List Σ
    st    : Q
    scan  : Σ
    right : List Σ

-- ────────────────────────────────────────────────────────────────────
-- §2 执行面（step / runN——燃料形总函数）
-- ────────────────────────────────────────────────────────────────────

-- 一步演化（halt 态自持；顶层辅助形——with-where 作用域病规避）
-- 顶层辅助（where 签名视域病规避——升顶层显式形）
leftLof : {Q Σ : Set} → Q → Σ → List Σ → Σ → List Σ → TConfig Q Σ
leftLof s' w' []       a r = mkTC [] s' w' (a ∷ r)
leftLof s' w' (x ∷ xs) a r = mkTC xs s' x (w' ∷ a ∷ r)

hdOf : {Σ : Set} → Σ → List Σ → Σ
hdOf b []      = b
hdOf _ (x ∷ _) = x

tlOf : {Σ : Set} → List Σ → List Σ
tlOf []       = []
tlOf (_ ∷ xs) = xs

moveH : {Q Σ : Set} → (blank : Σ) → (Q × Σ × Dir) → List Σ → Σ → List Σ → TConfig Q Σ
moveH b (s' , w' , L) l a r = leftLof s' w' l a r
moveH b (s' , w' , R) l a r = mkTC (w' ∷ l) s' (hdOf b r) (tlOf r)

stepH : {Q Σ : Set} → (M : TM Q Σ) → (blank : Σ) → Bool → TConfig Q Σ → TConfig Q Σ
stepH M b true  c = c
stepH M b false (mkTC l s a r) = moveH b (TM.δ M s a) l a r

step : {Q Σ : Set} → (M : TM Q Σ) → (blank : Σ) → TConfig Q Σ → TConfig Q Σ
step M b c = stepH M b (TM.halt M (TConfig.st c)) c

-- 燃料形多步执行（runN n = 至多 n 步——诚实设计：停机性不可判定故无总化 run）
runN : {Q Σ : Set} → (M : TM Q Σ) → (blank : Σ) → ℕ → TConfig Q Σ → TConfig Q Σ
runN M b zero    c = c
runN M b (suc n) c = goN (TM.halt M (TConfig.st c))
  where
  goN : Bool → _
  goN true  = c
  goN false = runN M b n (step M b c)

-- ────────────────────────────────────────────────────────────────────
-- §3 计算性声明面（关系形——深件立界注记的锚）
-- ────────────────────────────────────────────────────────────────────

-- 停机于配置谓词（燃料形观察面）
HaltsAt : {Q Σ : Set} → (M : TM Q Σ) → (b : Σ) → ℕ → TConfig Q Σ → Set
HaltsAt M b n c = TM.halt M (TConfig.st (runN M b n c)) ≡ true

-- 计算性声明：M 在输入 in（右带）上以输出 out 停机——存在燃料 n
-- （构造性形态：携带燃料的见证 record——深件面见 §5 立界）
record Computes {Q Σ : Set} (M : TM Q Σ) (b : Σ) (inp outp : List Σ) : Set where
  field
    fuel   : ℕ
    halted : TM.halt M (TConfig.st (runN M b fuel (mkTC [] (TM.q₀ M) b inp))) ≡ true
    output : TConfig.right (runN M b fuel (mkTC [] (TM.q₀ M) b inp)) ≡ outp   -- 注：outp = 终局右带（全带语义随立界件）

-- ────────────────────────────────────────────────────────────────────
-- §4 最小实例与核对层（数据形 refl）
-- ────────────────────────────────────────────────────────────────────

-- 状态/字母两元形
data Q2 : Set where
  q0 qh : Q2

data AB : Set where
  z o : AB   -- z 兼空白符

-- 最小停机机：一步即停（δ 恒转停机态；写出符号不变）
tm-min : TM Q2 AB
tm-min = record { δ = δm ; q₀ = q0 ; halt = haltm }
  where
  δm : Q2 → AB → Q2 × AB × Dir
  δm q0 a = (qh , a , R)
  δm qh a = (qh , a , R)
  haltm : Q2 → Bool
  haltm q0 = false
  haltm qh = true

cfg0 : TConfig Q2 AB
cfg0 = mkTC [] q0 z (o ∷ [])

-- 核对①：一步后转停机态（δ q0 z = (qh , z , R)——右移后 scan=o）
check-step1 : step tm-min z cfg0 ≡ mkTC (z ∷ []) qh o []
check-step1 = refl

-- 核对②：runN 1 步即停于停机态
check-run1 : TConfig.st (runN tm-min z 1 cfg0) ≡ qh
check-run1 = refl

-- 核对③：停机态自持（runN 10 与 runN 1 同局——halt 态冻结）
check-halt-freeze : runN tm-min z 10 cfg0 ≡ runN tm-min z 1 cfg0
check-halt-freeze = refl

-- 核对④：Computates 见证最小例（fuel=1）
check-computes : Computes tm-min z (o ∷ []) []
check-computes = record { fuel = 1 ; halted = refl ; output = refl }

-- ────────────────────────────────────────────────────────────────────
-- §5 立界注记（深件诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   Church-Turing 论题（TM 计算性=递归函数=λ 可定义性）——哲学-数学深件；
-- (ii)  停机问题不可判定（对角化）——独立批 200-300 行；
-- (iii) 通用图灵机构造（编码+解释器）——300+ 行深件；
-- (iv)  DFA ⇌ TM 等价（正则语言可识别性）——中件 ~100-150（衔接 DFA e267d383）；
-- (v)   Computates 与 PartialRecursive 面的对齐（可计算函数一般理论）。
