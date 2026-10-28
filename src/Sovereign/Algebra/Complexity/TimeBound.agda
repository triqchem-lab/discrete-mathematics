{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.TimeBound
-- 时间计账基元——PvsNP 程序 W1 计算模型层的第 1 件（路径乙：带计账函数层）
--
-- 数学背景：经典复杂度论中「算法在 f(n) 步内停机」需要计算模型（TM/RAAM）。
-- 本层取「带显式步数簿记的结构递归函数」为计算模型（路径乙，2026-10-28 裁定）：
--   计算体返回 Counted A = 值 × 本次求值真实消耗的步数（函数自己记账）；
--   多项式界 = ∃ p : ℕ → ℕ，p 单调（Mono）且正（Pos）；
--   时间界 = steps c ≤ p n（n = 输入规模），由对输入的结构归纳证明。
-- 这是 runN 燃料形（Automata.TuringMachine §2）在函数层的对偶：runN 的燃料
-- 是**外部供给的停机保证**，Counted 的 steps 是**内部产出的消耗账目**——
-- 两者相容（「Agda 函数 → TM 编码」桥）属立界项，见文尾。
--
-- 分级标注约定（全库诚实分级纪律）：
--   〔结构定义〕= 数据/record 定义；〔结构证明〕= 对输入结构归纳；
--   〔refl 枚举〕= 有限情形逐点 refl；〔立界注记〕= 深件边界，不设空壳签名。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.TimeBound where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m≤n+m; m≤n⇒m≤1+n; +-comm; *-suc)
open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)

-- ────────────────────────────────────────────────────────────────────
-- §1 计账值 Counted〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 带步数簿记的求值结果：value = 求值结果，steps = 本次求值真实消耗的步数。
-- steps 由计算体在结构递归中逐点累加（见 SATMember.satFormulaC 范式），
-- 不是外部断言——计账嵌入函数本身，账目即定义的一部分。
record Counted (A : Set) : Set where
  constructor cnt
  field
    value : A
    steps : ℕ

open Counted public

-- 步数界谓词：c 的账目不超过 k。
StepsLE : ∀ {A} → Counted A → ℕ → Set
StepsLE c k = steps c ≤ k

-- 界与值无关（提取引理）：同账目换值不改界
StepsLE-irrelevant-value : ∀ {A} (a a′ : A) (k k′ : ℕ)
                         → StepsLE {A = A} (cnt a k) k′ → StepsLE (cnt a′ k) k′
StepsLE-irrelevant-value a a′ k k′ h = h

-- ────────────────────────────────────────────────────────────────────
-- §2 多项式界的两个可证谓词：Mono / Pos〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 单调：输入规模不降则界不降（复杂度界经典要求）
Mono : (ℕ → ℕ) → Set
Mono p = ∀ {a b} → a ≤ b → p a ≤ p b

-- 正性：界恒 ≥ 1（排除退化的零界——保证「多项式增长」非空洞）
Pos : (ℕ → ℕ) → Set
Pos p = ∀ n → 1 ≤ p n

-- ────────────────────────────────────────────────────────────────────
-- §3 ≤-算术小引理库〔结构证明〕（自证版——只依赖 +/* 定义性，零 API 风险）
-- ────────────────────────────────────────────────────────────────────

-- 左加单调：a ≤ b ⇒ c + a ≤ c + b
mono-+ˡ : ∀ c {a b} → a ≤ b → c + a ≤ c + b
mono-+ˡ zero    h = h
mono-+ˡ (suc c) h = s≤s (mono-+ˡ c h)

-- 右加单调：a ≤ b ⇒ a + c ≤ b + c
mono-+ʳ : ∀ c {a b} → a ≤ b → a + c ≤ b + c
mono-+ʳ c {a} {b} h =
  ≤-trans (≤-reflexive (+-comm a c))
          (≤-trans (mono-+ˡ c h)
                   (≤-reflexive (sym (+-comm b c))))

-- 乘法对右参数单调：a ≤ b ⇒ k * a ≤ k * b
--   suc k * a = a + k*a ≤ b + k*b = suc k * b（两项各自单调，加法拼合）
mono-*ˡ : ∀ {a b} k → a ≤ b → k * a ≤ k * b
mono-*ˡ zero    h = z≤n
mono-*ˡ {a} {b} (suc k) h =
  ≤-trans (mono-+ʳ (k * a) h) (mono-+ˡ _ (mono-*ˡ k h))

-- 正因子放大：k ≥ 1 ⇒ j ≤ j * k
--   链：suc j ≤ suc (j*k) ≤ k + j*k = suc j * k（k ≥ 1；suc j*k 定义性 = k + j*k）
le-mul : ∀ j k → 1 ≤ k → j ≤ j * k
le-mul zero    k k≥1 = z≤n
le-mul (suc j) k k≥1 =
  ≤-trans (s≤s (le-mul j k k≥1))
          (mono-+ʳ (j * k) k≥1)

-- ────────────────────────────────────────────────────────────────────
-- §4 多项式界实例：suc 与「常偏移 + 恒等」〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- p n = suc n：最基本线性界
polySuc : ℕ → ℕ
polySuc = suc

polySuc-mono : Mono polySuc
polySuc-mono {a} {b} a≤b = s≤s a≤b

polySuc-pos : Pos polySuc
polySuc-pos n = s≤s z≤n

-- p n = (suc c) + n：正偏移线性界
polyOffset : ℕ → ℕ → ℕ
polyOffset c n = suc c + n

polyOffset-mono : ∀ c → Mono (polyOffset c)
polyOffset-mono c {a} {b} a≤b = s≤s (mono-+ˡ c a≤b)
  -- suc c + a = suc (c + a)，s≤s 保序

polyOffset-pos : ∀ c → Pos (polyOffset c)
polyOffset-pos c n = ≤-trans (s≤s z≤n) (s≤s (m≤m+n c n))
  -- 1 ≤ suc c ≤ suc (c + n) = polyOffset c n

-- ────────────────────────────────────────────────────────────────────
-- §5 界传导（界单调下，小界换大界）〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

bound-mono : ∀ {A} (c : Counted A) (p : ℕ → ℕ) {n n′ : ℕ}
           → Mono p → StepsLE c (p n) → n ≤ n′ → StepsLE c (p n′)
bound-mono c p p-mono h n≤n′ = ≤-trans h (p-mono n≤n′)

-- 常用特化：n ≤ suc n 时界不降
bound-step : ∀ {A} (c : Counted A) (p : ℕ → ℕ) {n : ℕ}
           → Mono p → StepsLE c (p n) → StepsLE c (p (suc n))
bound-step c p p-mono h = bound-mono c p p-mono h (m≤n⇒m≤1+n ≤-refl)

-- ────────────────────────────────────────────────────────────────────
-- §6 计账组合子（SAT 验证器的积木）〔结构定义 + refl 展开〕
-- ────────────────────────────────────────────────────────────────────

-- 零步纯值
cntPure : ∀ {A} → A → Counted A
cntPure a = cnt a 0

-- 布尔或（贪婪全求值形：步数相加，无短路——计账确定性优先）
orC : Counted Bool → Counted Bool → Counted Bool
orC (cnt b₁ s₁) (cnt b₂ s₂) = cnt (b₁ ∨ b₂) (s₁ + s₂)

-- 布尔三或（3-SAT 子句形状；右结合与 Data.Bool._∨_ 定义序一致）
or3C : Counted Bool → Counted Bool → Counted Bool → Counted Bool
or3C (cnt b₁ s₁) (cnt b₂ s₂) (cnt b₃ s₃) = cnt (b₁ ∨ (b₂ ∨ b₃)) (s₁ + (s₂ + s₃))

-- 布尔且（公式 = 子句合取；步数相加，无短路）
andC : Counted Bool → Counted Bool → Counted Bool
andC (cnt b₁ s₁) (cnt b₂ s₂) = cnt (b₁ ∧ b₂) (s₁ + s₂)

-- 值/账目展开（模式匹配后定义性成立）
value-orC : ∀ c₁ c₂ → value (orC c₁ c₂) ≡ (value c₁ ∨ value c₂)
value-orC (cnt _ _) (cnt _ _) = refl

steps-orC : ∀ c₁ c₂ → steps (orC c₁ c₂) ≡ (steps c₁ + steps c₂)
steps-orC (cnt _ _) (cnt _ _) = refl

value-andC : ∀ c₁ c₂ → value (andC c₁ c₂) ≡ (value c₁ ∧ value c₂)
value-andC (cnt _ _) (cnt _ _) = refl

steps-andC : ∀ c₁ c₂ → steps (andC c₁ c₂) ≡ (steps c₁ + steps c₂)
steps-andC (cnt _ _) (cnt _ _) = refl

value-or3C : ∀ c₁ c₂ c₃
           → value (or3C c₁ c₂ c₃) ≡ (value c₁ ∨ (value c₂ ∨ value c₃))
value-or3C (cnt _ _) (cnt _ _) (cnt _ _) = refl

steps-or3C : ∀ c₁ c₂ c₃
           → steps (or3C c₁ c₂ c₃) ≡ (steps c₁ + (steps c₂ + steps c₃))
steps-or3C (cnt _ _) (cnt _ _) (cnt _ _) = refl

-- ────────────────────────────────────────────────────────────────────
-- §7 核对层〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

check-orC : value (orC (cnt true 1) (cnt false 2)) ≡ true
check-orC = refl

check-orC-steps : steps (orC (cnt true 1) (cnt false 2)) ≡ 3
check-orC-steps = refl

check-or3C-steps : steps (or3C (cnt true 1) (cnt true 1) (cnt false 1)) ≡ 3
check-or3C-steps = refl

check-bound-mono : StepsLE (cnt true 1) (polySuc 5)
check-bound-mono = s≤s z≤n

-- ────────────────────────────────────────────────────────────────────
-- §8 立界注记（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   Counted.steps（内部账目）与 TuringMachine.runN 燃料（外部供给）的
--       对应桥——「结构递归 Agda 函数 → TM 编码」= Church-Turing 型深件，
--       与经典 P 定义的计算模型对齐；独立批（W1a 后续）。
-- (ii)  本层 steps 是精确账目（等式级，见 SATMember §2 steps-引理），
--       非大 O 渐近记号；渐近层（Big-O 关系 ≃）立界。
-- (iii) 计账组合子的组合律/单层面（Counted ⟹ 计账半环）——工程扩展件。

-- 0 postulate / 0 hole / 0 Terminate-check 溢出。
-- 本文件由 agda +RTS -M8G -H6G -A128M -RTS 编译，EXIT=0 为完成判据。
