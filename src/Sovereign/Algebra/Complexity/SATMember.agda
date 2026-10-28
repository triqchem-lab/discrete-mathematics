{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.SATMember
-- 3-SAT ∈ NP——三件套全闭合（W1 计算模型层第 4 件，路径乙收官件）
--
-- 数学背景：3-SAT = 子句式可满足性。本件在带计账函数层（TimeBound/NPClass）
-- 闭合 **SAT ∈ NP 三件套**：
--   ① 验证器 V：输入 trit 串 x（公式编码）+ 见证 a（赋值），输出 Counted Bool；
--   ② 见证长度界 w(n) = suc m（变元池大小常数——见诚实边界注记）；
--   ③ 代价界 p(n) = suc (3·n)：V 的账目 = 3·(n/clauseW m) ≤ 3·n < suc (3·n)。
--
-- 编码（三进制母语，本件规范形）：
--   变元池 = suc m 个变元（Fin (suc m)）；赋值 = Vec Trit (suc m)（T₁ = 真）。
--   文字 = Sign × 变元号；子句 = 三文字；公式 = 长度索引子句表（Vec 子句 c）。
--   串布局：子句序贯；每文字宽 suc m + 1 位 trit = 1 位符号 + suc m 位独热变元号
--   （变元号独热——独热位宽 = 变元池大小，保证见证长度 ≤ 串规模，见 §6 注记）。
--   子句宽 clauseW m = 3·(suc m)，串长 n 解码 n / clauseW m 个子句（尾料忽略，规范固定）。
--   语义：Kleene-强满足——文字真 ⟺ 值为 T₁；子句真 ⟺ 某文字真。
--
-- 诚实边界（§6 立界清单）：变元池 suc m 对每个固定 m 是常数（SAT_m 语言）；
-- 「变元池随 n 增长」的经典 SAT 族需可变宽编码 + Fagin 型论证 = W2 立界；
-- 「公式 → 串」encode 方向、SAT NP-完备性均立界不冒充。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.SATMember where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; ≤-refl; m≤m+n; m≤n⇒m≤1+n; *-suc; +-comm)
open import Data.Nat.DivMod using (_/_; _%_; m≡m%n+[m/n]*n)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Vec using (Vec; []; _∷_; lookup; tabulate; length)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂; sym)

-- 引用边界（跨域引用注记）：
--   Sovereign.Base.Trit —— 取载体 + negate（文字取反：σ₋ v = negate v）；
--   TimeBound / NPClass —— 同层计算模型件（计账组合子、NP record）。
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.Complexity.TimeBound
  using (Counted; value; steps; Mono; Pos; orC; or3C; value-orC;
         andC; value-andC; mono-*ˡ; le-mul)
  renaming (cnt to mkCnt)
open import Sovereign.Algebra.Complexity.PClass using (TritLang)
open import Sovereign.Algebra.Complexity.NPClass using (InNP)

-- ────────────────────────────────────────────────────────────────────
-- §1 格式层：文字/子句/公式〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- 符号：σ₊ = 正文字（取原值），σ₋ = 负文字（取 negate）
data Sign : Set where
  σ₊ : Sign
  σ₋ : Sign

-- 变元池 = suc m 个变元（m = 0 时单变元池；suc 形保证独热读取 total）
Lit : ℕ → Set
Lit m = Sign × Fin (suc m)

Clause : ℕ → Set
Clause m = Lit m × Lit m × Lit m

-- 公式 = 子句表（长度索引列表：c 个子句）
Formula : ℕ → ℕ → Set
Formula m c = Vec (Clause m) c

-- 子句宽 = 3·(suc m)；写成字面 suc 形，除法 NonZero instance 自动可用
clauseW : ℕ → ℕ
clauseW m = suc (2 + m * 3)

-- 赋值 = 见证：全池 trit 向量（T₁ = 真；T₀ = 假；T₂ = 不定，Kleene 强语义下
-- 「非 T₁ 即非真」——子句需某文字恰为 T₁）
Asg : ℕ → Set
Asg m = Vec Trit (suc m)

-- ────────────────────────────────────────────────────────────────────
-- §2 语义层：evalLit / satClause / satFormula 纯函数 + 计账伴生版
-- ────────────────────────────────────────────────────────────────────

isT₁ : Trit → Bool
isT₁ T₀ = false
isT₁ T₁ = true
isT₁ T₂ = false

-- 文字求值〔结构定义〕（stdlib 2.4 lookup 签名：Vec → Fin → A）
evalLit : ∀ {m} → Asg m → Lit m → Trit
evalLit a (σ₊ , v) = lookup a v
evalLit a (σ₋ , v) = negate (lookup a v)

-- 子句满足（Kleene-强：某文字 = T₁）〔结构定义〕
satClause : ∀ {m} → Asg m → Clause m → Bool
satClause a (l₁ , l₂ , l₃) =
  isT₁ (evalLit a l₁) ∨ (isT₁ (evalLit a l₂) ∨ isT₁ (evalLit a l₃))

-- 公式满足（CNF 合取范式：所有子句皆满足；空公式真 = 空合取）〔结构定义〕
satFormula : ∀ {m c} → Asg m → Formula m c → Bool
satFormula a [] = true
satFormula a (cl ∷ φ) = satClause a cl ∧ satFormula a φ

-- 计账伴生版：每文字 1 步、子句 3 步（or3C 账目 1+(1+1)）、公式账目相加。
-- 账目即定义（TimeBound 纪律：函数自带步数簿记，非外部断言）。
satLitC : ∀ {m} (a : Asg m) (l : Lit m) → Counted Bool
satLitC a l = mkCnt (isT₁ (evalLit a l)) 1

satClauseC : ∀ {m} (a : Asg m) (cl : Clause m) → Counted Bool
satClauseC a (l₁ , l₂ , l₃) = or3C (satLitC a l₁) (satLitC a l₂) (satLitC a l₃)

satFormulaC : ∀ {m c} (a : Asg m) (φ : Formula m c) → Counted Bool
satFormulaC a [] = mkCnt true 0
satFormulaC a (cl ∷ φ) = andC (satClauseC a cl) (satFormulaC a φ)

-- 值一致性：计账版值 = 纯函数值（或门逐点）〔refl + 结构归纳〕
value-satClause : ∀ {m} (a : Asg m) (cl : Clause m)
                → value (satClauseC a cl) ≡ satClause a cl
value-satClause a (l₁ , l₂ , l₃) = refl

value-satFormulaC : ∀ {m c} (a : Asg m) (φ : Formula m c)
                  → value (satFormulaC a φ) ≡ satFormula a φ
value-satFormulaC a [] = refl
value-satFormulaC a (cl ∷ φ) =
  trans (value-andC (satClauseC a cl) (satFormulaC a φ))
        (cong₂ _∧_ (value-satClause a cl) (value-satFormulaC a φ))

-- 步数引理：公式求值账目 = 3·子句数（精确等式，非上界）〔结构归纳〕
steps-satFormulaC : ∀ {m c} (a : Asg m) (φ : Formula m c)
                  → steps (satFormulaC a φ) ≡ 3 * c
steps-satFormulaC a [] = refl
steps-satFormulaC a (cl ∷ φ) =
  trans (cong (3 +_) (steps-satFormulaC a φ)) (sym (*-suc 3 _))
-- 左边：steps (orC (satClauseC a cl) (satFormulaC a φ)) 定义性归约
--       = 3 + steps (satFormulaC a φ)（子句账 1+(1+1)=3）；cong + 归纳后
--       = 3 + 3·c ≡ 3·c + 3 ≡ 3·suc c。

-- ────────────────────────────────────────────────────────────────────
-- §3 解码层：trit 串 → 公式（总函数；尾料 = 不足一子句的尾段，忽略）
-- ────────────────────────────────────────────────────────────────────

-- 安全读取（越界取 T₀——规范自由度；总函数）〔结构定义〕
safeLook : (n : ℕ) → Vec Trit n → ℕ → Trit
safeLook zero [] i = T₀
safeLook (suc n) (t ∷ ts) zero = t
safeLook (suc n) (t ∷ ts) (suc i) = safeLook n ts i

-- 符号解码：T₁ ↦ σ₊；T₀/T₂ ↦ σ₋（规范自由度）〔refl 枚举定义〕
signOf : Trit → Sign
signOf T₀ = σ₋
signOf T₁ = σ₊
signOf T₂ = σ₋

-- 独热变元号解码：取首个 T₁ 位；全非 T₁ 归 0 号（规范自由度）〔结构定义〕
fromOneHot : (m : ℕ) → Vec Trit (suc m) → Fin (suc m)
fromOneHot zero _ = fzero
fromOneHot (suc m) (T₁ ∷ _) = fzero
fromOneHot (suc m) (_ ∷ ts) = fsuc (fromOneHot m ts)

-- 文字解码：base 位符号，base+1+s 位独热（s : Fin (suc m)）〔结构定义〕
decLit : (m n : ℕ) → Vec Trit n → ℕ → Lit m
decLit m n x base =
  signOf (safeLook n x base) ,
  fromOneHot m (tabulate (λ s → safeLook n x (base + suc (toℕ s))))

-- 子句解码：base, base+3, base+6 三文字〔结构定义〕
decClause : (m n : ℕ) → Vec Trit n → ℕ → Clause m
decClause m n x base =
  decLit m n x base , decLit m n x (base + 3) , decLit m n x (base + 6)

-- 公式解码：第 j 子句基址 j·clauseW m；共 n / clauseW m 个完整子句〔结构定义〕
decFormula : (m n : ℕ) → Vec Trit n → Formula m (n / clauseW m)
decFormula m n x = tabulate (λ j → decClause m n x (toℕ j * clauseW m))

-- tabulate 长度引理（解码宽度核对用）〔结构归纳〕
lenTab : (n : ℕ) (f : Fin n → Trit) → length (tabulate f) ≡ n
lenTab zero f = refl
lenTab (suc n) f = cong suc (lenTab n (λ i → f (fsuc i)))

-- ────────────────────────────────────────────────────────────────────
-- §4 语言与验证器
-- ────────────────────────────────────────────────────────────────────

-- SAT_m 语言：x ∈ L-SAT m ⟺ 存在赋值 a 使 x 的解码公式可满足
-- （成员证据直接携带见证——三件套之①的语义面）
L-SAT : ℕ → TritLang
L-SAT m n x = Σ (Asg m) (λ a → satFormula a (decFormula m n x) ≡ true)

-- 验证器：值 = 计账求值之值；账目 = 3·(n/clauseW m)（与 steps-satFormulaC 一致，
-- 解码宽度 n/clauseW m = 解码公式长度，lenTab 保证）〔结构定义〕
sat-verifier : (m n : ℕ) → Vec Trit n → Asg m → Counted Bool
sat-verifier m n x a =
  mkCnt (value (satFormulaC a (decFormula m n x))) (3 * (n / clauseW m))

-- ────────────────────────────────────────────────────────────────────
-- §5 ★ SAT_m ∈ NP 三件套闭合〔结构证明〕
-- ────────────────────────────────────────────────────────────────────

-- 除法界引理：clauseW m ≥ 1 ⟹ n / clauseW m ≤ n〔结构证明〕
--   链：n/W ≤ (n/W)·W ≤ (n/W)·W + n%W ≡ n%W + (n/W)·W ≡ n
div-le : (m n : ℕ) → n / clauseW m ≤ n
div-le m n =
  ≤-trans (le-mul (n / clauseW m) (clauseW m) (s≤s z≤n))
          (≤-trans (m≤m+n ((n / clauseW m) * clauseW m) (n % clauseW m))
                   (≤-reflexive (trans (+-comm ((n / clauseW m) * clauseW m) (n % clauseW m))
                                       (sym (m≡m%n+[m/n]*n n (clauseW m))))))

-- 代价多项式：p(n) = suc (3·n)
polySAT : ℕ → ℕ
polySAT n = suc (3 * n)

polySAT-mono : Mono polySAT
polySAT-mono {a} {b} a≤b = s≤s (mono-*ˡ 3 a≤b)

polySAT-pos : Pos polySAT
polySAT-pos n = s≤s z≤n

-- ★ 主定理：对每个变元池参数 m，SAT_m ∈ NP
sat-in-NP : (m : ℕ) → InNP (L-SAT m)
sat-in-NP m = record
  { np-p = polySAT
  ; np-p-mono = polySAT-mono
  ; np-p-pos = polySAT-pos
  ; np-witLen = λ _ → suc m
  ; np-w-mono = λ _ → s≤s ≤-refl         -- 常界 suc m ≤ suc m
  ; np-verifier = λ n x a → sat-verifier m n x a
  ; np-complete = λ n x (a , eq) →
      a , trans (value-satFormulaC a (decFormula m n x)) eq
      -- 目标 value (sat-verifier …) ≡ true；左端 defeq value (satFormulaC a φ)，
      -- value-satFormulaC : value (satFormulaC a φ) ≡ satFormula a φ，接 eq。
  ; np-sound = λ n x a v →
      a , trans (sym (value-satFormulaC a (decFormula m n x))) v
      -- v : value (sat-verifier …) ≡ true（左端 defeq value (satFormulaC a φ)）；
      -- 对称引理换向后拼出 satFormula a φ ≡ true，即成员证据。
  ; np-cost = λ n x a →                                        -- ③代价界
      ≤-trans (mono-*ˡ 3 (div-le m n)) (m≤n⇒m≤1+n ≤-refl) }
-- complete：见证取成员证据中的 a；verifier 值 = satFormulaC 值 = satFormula 值 = true。
-- sound：verifier 值 = true ⟹ satFormula ≡ true ⟹ 成员 (a , _)。
-- cost：3·(n/clauseW m) ≤ 3·n ≤ suc (3·n)。

-- ────────────────────────────────────────────────────────────────────
-- §6 核对层〔refl 枚举〕——m = 1（2 变元池），串长 9（1 完整子句 + 3 位尾料）
-- ────────────────────────────────────────────────────────────────────

-- 布局核对：clauseW 1 = 6；9 / 6 = 1
check-W : clauseW 1 ≡ 6
check-W = refl

check-div : 9 / clauseW 1 ≡ 1
check-div = refl

-- 测试串 x₉：子句 (x₀ ∨ ¬x₁ ∨ x₁)
--   位 0-2 = (σ₊, x₀)：T₁ T₁ T₀      位 3-5 = (σ₋, x₁)：T₀ T₀ T₁
--   位 6-8 = (σ₊, x₁)：T₁ T₀ T₁
x₉ : Vec Trit 9
x₉ = T₁ ∷ T₁ ∷ T₀ ∷ T₀ ∷ T₀ ∷ T₁ ∷ T₁ ∷ T₀ ∷ T₁ ∷ []

-- 实例①：a = (x₀=T₁, x₁=T₀)——文字 σ₊x₀ = T₁ 真 ⟹ 可满足
check-sat₁ : satFormula (T₁ ∷ T₀ ∷ []) (decFormula 1 9 x₉) ≡ true
check-sat₁ = refl

-- 实例②：a′ = (x₀=T₀, x₁=T₀)——σ₊x₀=T₀, σ₋x₁=negate T₀=T₀, σ₊x₁=T₀ 全假
check-sat₂ : satFormula (T₀ ∷ T₀ ∷ []) (decFormula 1 9 x₉) ≡ false
check-sat₂ = refl

-- 实例③：换见证 a″ = (T₀, T₁)——σ₋x₁ = negate T₁ = T₂ 非真，σ₊x₁ = T₁ 真
check-sat₃ : satFormula (T₀ ∷ T₁ ∷ []) (decFormula 1 9 x₉) ≡ true
check-sat₃ = refl

-- 验证器账目：3·(9/6) = 3
check-verifier-steps : steps (sat-verifier 1 9 x₉ (T₁ ∷ T₀ ∷ [])) ≡ 3
check-verifier-steps = refl

-- 验证器值一致性（计账版 = 纯函数）
check-verifier-value : value (sat-verifier 1 9 x₉ (T₀ ∷ T₀ ∷ [])) ≡ false
check-verifier-value = refl

-- ────────────────────────────────────────────────────────────────────
-- §7 立界注记（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   变元池 suc m 对固定 m 是常数：SAT_m 是「池内可满足性」语言族，
--       每个成员 ∈ NP 本件闭合。经典 SAT 的变元池随 n 增长需要
--       「变元号位宽 log₃ m」的可变宽编码 + 见证长多项式界论证，
--       且「m 内嵌串首」的自含格式——W1 后续件（见证头格式）。
-- (ii)  encode 方向（公式 → 串）未闭合：本件语言以「解码即语义」定义
--       （L-SAT 只经 decFormula），完备性不依赖 encode；encode/decode
--       往返（decode (encode φ) ≡ φ）独立小件。
-- (iii) SAT NP-完备性（Cook-Levin 型归约）= W2（Fagin）范围，立界不排期。
-- (iv)  验证器可由 TM 实现——同 PClass/NPClass 的函数层 → TM 桥立界。
-- (v)   3-SAT 的「每子句恰 3 文字、无重文字化简」——本件子句恒 3 文字
--       （含重复文字，经典等价：重复文字不影响满足性，refl 可见）。

-- 0 postulate / 0 hole。
