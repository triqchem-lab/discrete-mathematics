{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.CNF
-- 一般 CNF（子句长度可变）——Cook–Levin 前置 M1a
--
-- 【为什么单独一层】库内 `SATMember.Formula` 是**固定 3-CNF**：`Clause m = Lit m × Lit
-- m × Lit m`（SATMember:62）。而 Cook–Levin 的 tableau 会产生 4–7 文字的子句
-- （每格「至少一个符号」= |Γ|、每刻「至少一个状态」= |Q|、转移局部一致性 5–7），
-- 这些形状在 3-CNF 里**表达不出来**。本件把「子句 = 文字表、公式 = 子句表」这一层
-- 先立起来：语义与 SATMember 逐点一致，并把 3-CNF 嵌入为特例（§4 保真定理）。
--
-- 【为什么用 List 而不是 Vec】3-CNF 的 `Formula m c = Vec (Clause m) c` 是长度索引的，
-- 拼接 `Vec _ a` 与 `Vec _ b` 得 `Vec _ (a + b)` ⟹ 构造 O(p²) 个子句要一路携带
-- `+-assoc`/`+-comm`。tableau 正是「拼 O(p²) 个子句」，用 Vec 等于自找算术沼泽。
-- List 上的 `++` 与 `satClause'`/`satFormula'` 的结构归纳逐条对齐（§2 的两条拼接
-- 引理 + §2 的单调引理），这是本层的**设计理由**，不是风格偏好。
--
-- 【语义口径】与 SATMember 完全一致：Kleene-强（某文字 = T₁ 才算满足），
--   · 空子句 = false（空析取，对应「不可满足」）；
--   · 空公式 = true（空合取）。
--   两者都使 §2 的拼接引理在 `[]` 上成立（`false ∨ b ≡ b`、`true ∧ b ≡ b`，定义性）。
--
-- 【计账口径】沿用 SATMember：每个文字 1 步、OR/AND 节点不另计 ⟹
--   子句账 = 文字数（精确等式），公式账 = 全部文字数 = `length (concat φ)`（精确等式）。
--   与 3-CNF 的 `steps-satFormulaC ≡ 3 * c` 相容（3 文字/子句时二者一致）。
--
-- 分级约定：〔结构定义〕/〔结构证明〕/〔refl 枚举〕/〔立界注记〕（同 TimeBound）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.CNF where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Bool.Properties using (∨-assoc; ∧-assoc; ∨-identityʳ)
open import Data.List using (List; []; _∷_; _++_; concat; length)
open import Data.List.Properties using (length-++)
open import Data.Vec using (Vec) renaming ([] to vNil; _∷_ to _v∷_)
open import Data.Product using (_,_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

-- 引用边界（跨域引用注记）：
--   Sovereign.Base.Trit —— 载体与 negate（与 SATMember 同一口径）；
--   Sovereign.Algebra.Complexity.TimeBound —— 计账组合子 orC/andC 与其 value/steps 引理；
--   Sovereign.Algebra.Complexity.SATMember —— Lit/Asg/evalLit/isT₁ + 3-CNF 的
--     Clause/Formula/satClause/satFormula（本件不重定义任何语义，只泛化子句形状）。
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; negate)
open import Sovereign.Algebra.Complexity.TimeBound
  using (Counted; value; steps; orC; andC;
         value-orC; steps-orC; value-andC; steps-andC)
  renaming (cnt to mkCnt)
open import Sovereign.Algebra.Complexity.SATMember
  using (Sign; σ₊; σ₋; Lit; Asg; evalLit; isT₁; Clause; Formula; satClause; satFormula)

-- ────────────────────────────────────────────────────────────────────
-- §1 一般 CNF：类型 + 语义〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

Clause' : ℕ → Set
Clause' m = List (Lit m)

Formula' : ℕ → Set
Formula' m = List (Clause' m)

-- 文字真值（与 SATMember.satLitC 同口径：T₁ 才算真）
satLit' : ∀ {m} → Asg m → Lit m → Bool
satLit' a l = isT₁ (evalLit a l)

satClause' : ∀ {m} → Asg m → Clause' m → Bool
satClause' a []       = false
satClause' a (l ∷ ls) = satLit' a l ∨ satClause' a ls

satFormula' : ∀ {m} → Asg m → Formula' m → Bool
satFormula' a []        = true
satFormula' a (cl ∷ φ)  = satClause' a cl ∧ satFormula' a φ

-- ────────────────────────────────────────────────────────────────────
-- §2 拼接与单调〔结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 这三条是本层存在的理由：tableau 要拼 O(p²) 个子句，拼接必须在定义层可用、
-- 不能带来长度算术。注意两个拼接引理的**折向**：`satClause'` 是右折
-- `b₁ ∨ (b₂ ∨ … ∨ false)`，故 `++` 的拼接需要一次 ∨-assoc（不是分案）。

satClause'-++ : ∀ {m} (a : Asg m) (xs ys : Clause' m)
              → satClause' a (xs ++ ys) ≡ (satClause' a xs ∨ satClause' a ys)
satClause'-++ a []       ys = refl
satClause'-++ a (x ∷ xs) ys =
  trans (cong (satLit' a x ∨_) (satClause'-++ a xs ys))
        (sym (∨-assoc (satLit' a x) (satClause' a xs) (satClause' a ys)))

satFormula'-++ : ∀ {m} (a : Asg m) (φ ψ : Formula' m)
               → satFormula' a (φ ++ ψ) ≡ (satFormula' a φ ∧ satFormula' a ψ)
satFormula'-++ a []         ψ = refl
satFormula'-++ a (cl ∷ φ)   ψ =
  trans (cong (satClause' a cl ∧_) (satFormula'-++ a φ ψ))
        (sym (∧-assoc (satClause' a cl) (satFormula' a φ) (satFormula' a ψ)))

-- 子句追加文字不会由真变假（Tseitin 的回向会用到）
satClause'-mono : ∀ {m} (a : Asg m) (xs ys : Clause' m)
                → satClause' a xs ≡ true → satClause' a (xs ++ ys) ≡ true
satClause'-mono a xs ys h =
  trans (satClause'-++ a xs ys) (cong (_∨ satClause' a ys) h)

-- 空子句使公式恒假（= 该公式不可满足）
satFormula'-cons-false : ∀ {m} (a : Asg m) (φ : Formula' m)
                       → satFormula' a ([] ∷ φ) ≡ false
satFormula'-cons-false a φ = refl

-- ────────────────────────────────────────────────────────────────────
-- §3 计账伴生版〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 口径同 SATMember：每文字 1 步，OR/AND 节点不另计。于是子句账 = 文字数、
-- 公式账 = 全部文字数，都是**精确等式**（不是上界）。

satLit'C : ∀ {m} (a : Asg m) (l : Lit m) → Counted Bool
satLit'C a l = mkCnt (satLit' a l) 1

satClause'C : ∀ {m} (a : Asg m) (cl : Clause' m) → Counted Bool
satClause'C a []       = mkCnt false 0
satClause'C a (l ∷ ls) = orC (satLit'C a l) (satClause'C a ls)

satFormula'C : ∀ {m} (a : Asg m) (φ : Formula' m) → Counted Bool
satFormula'C a []       = mkCnt true 0
satFormula'C a (cl ∷ φ) = andC (satClause'C a cl) (satFormula'C a φ)

value-satClause'C : ∀ {m} (a : Asg m) (cl : Clause' m)
                  → value (satClause'C a cl) ≡ satClause' a cl
value-satClause'C a []       = refl
value-satClause'C a (l ∷ ls) =
  trans (value-orC (satLit'C a l) (satClause'C a ls))
        (cong₂ _∨_ refl (value-satClause'C a ls))

value-satFormula'C : ∀ {m} (a : Asg m) (φ : Formula' m)
                   → value (satFormula'C a φ) ≡ satFormula' a φ
value-satFormula'C a []       = refl
value-satFormula'C a (cl ∷ φ) =
  trans (value-andC (satClause'C a cl) (satFormula'C a φ))
        (cong₂ _∧_ (value-satClause'C a cl) (value-satFormula'C a φ))

steps-satClause'C : ∀ {m} (a : Asg m) (cl : Clause' m)
                  → steps (satClause'C a cl) ≡ length cl
steps-satClause'C a []       = refl
steps-satClause'C a (l ∷ ls) = cong suc (steps-satClause'C a ls)

-- 公式账 = 全部文字数（写成 concat 的长度，避免引入求和函数）
steps-satFormula'C : ∀ {m} (a : Asg m) (φ : Formula' m)
                   → steps (satFormula'C a φ) ≡ length (concat φ)
steps-satFormula'C a []       = refl
steps-satFormula'C a (cl ∷ φ) =
  trans (trans (steps-andC (satClause'C a cl) (satFormula'C a φ))
               (cong₂ _+_ (steps-satClause'C a cl) (steps-satFormula'C a φ)))
        (sym (length-++ cl))

-- ────────────────────────────────────────────────────────────────────
-- §4 3-CNF 嵌入〔结构定义 + 结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 每条 3-子句 ⟹ 一条 3-长子句；语义逐点保真（保真定理 §4 是 M3 的接缝：
-- tableau 在一般 CNF 里构造，最后一步落到 3-CNF 族时用本定理）。

clauseOf3 : ∀ {m} → Lit m → Lit m → Lit m → Clause' m
clauseOf3 l₁ l₂ l₃ = l₁ ∷ l₂ ∷ l₃ ∷ []

formulaOf3 : ∀ {m c} → Formula m c → Formula' m
formulaOf3 vNil                  = []
formulaOf3 ((l₁ , (l₂ , l₃)) v∷ φ) = clauseOf3 l₁ l₂ l₃ ∷ formulaOf3 φ

-- 差一个尾端的 `∨ false`：库内 satClause 是 `b₁ ∨ (b₂ ∨ b₃)`，本层是右折到 `false`
satClause'-3 : ∀ {m} (a : Asg m) (l₁ l₂ l₃ : Lit m)
             → satClause' a (clauseOf3 l₁ l₂ l₃) ≡ satClause a (l₁ , l₂ , l₃)
satClause'-3 a l₁ l₂ l₃ =
  cong (satLit' a l₁ ∨_) (cong (satLit' a l₂ ∨_) (∨-identityʳ (satLit' a l₃)))

formulaOf3-sat : ∀ {m c} (a : Asg m) (φ : Formula m c)
               → satFormula' a (formulaOf3 φ) ≡ satFormula a φ
formulaOf3-sat a vNil = refl
formulaOf3-sat a ((l₁ , (l₂ , l₃)) v∷ φ) =
  trans (cong (satClause' a (clauseOf3 l₁ l₂ l₃) ∧_) (formulaOf3-sat a φ))
        (cong₂ _∧_ (satClause'-3 a l₁ l₂ l₃) refl)

-- ────────────────────────────────────────────────────────────────────
-- §5 核对层〔refl 枚举〕（m = 0：单变元 x₀）
-- ────────────────────────────────────────────────────────────────────

-- 空子句 = 假、空公式 = 真（两条边界口径）
Cnf-check-empty-clause : satClause' (T₁ v∷ vNil) [] ≡ false
Cnf-check-empty-clause = refl

Cnf-check-empty-formula : satFormula' (T₁ v∷ vNil) [] ≡ true
Cnf-check-empty-formula = refl

-- 单文字子句：正文字真 / 负文字假（negate T₁ = T₂ ⟹ 非 T₁）
Cnf-check-unit-true : satClause' (T₁ v∷ vNil) ((σ₊ , fzero) ∷ []) ≡ true
Cnf-check-unit-true = refl

Cnf-check-unit-false : satClause' (T₁ v∷ vNil) ((σ₋ , fzero) ∷ []) ≡ false
Cnf-check-unit-false = refl

-- **3-CNF 表达不了**的形状：4 长子句（|Γ| = 4 的「至少一个符号」就是这个形状）
Cnf-check-four-lit :
  satClause' (T₁ v∷ vNil)
    ((σ₊ , fzero) ∷ (σ₋ , fzero)
       ∷ (σ₊ , fzero) ∷ (σ₋ , fzero) ∷ [])
  ≡ true
Cnf-check-four-lit = refl

-- 计账：4 文字 = 4 步（精确）
Cnf-check-steps-four :
  steps (satClause'C (T₁ v∷ vNil)
           ((σ₊ , fzero) ∷ (σ₋ , fzero)
              ∷ (σ₊ , fzero) ∷ (σ₋ , fzero) ∷ []))
  ≡ 4
Cnf-check-steps-four = refl

-- 3-CNF 嵌入：形状逐字（3 文字一条子句，保持顺序）
Cnf-check-of3 :
  formulaOf3 {0} {1} (((σ₊ , fzero) , (σ₋ , fzero)
                       , (σ₊ , fzero)) v∷ vNil)
  ≡ ((σ₊ , fzero) ∷ (σ₋ , fzero)
       ∷ (σ₊ , fzero) ∷ []) ∷ []
Cnf-check-of3 = refl

-- 3-CNF 嵌入：语义保真（同一条式子在两层都真）
Cnf-check-of3-sat :
  satFormula' (T₁ v∷ vNil)
    (formulaOf3 (((σ₊ , fzero) , (σ₋ , fzero)
                    , (σ₊ , fzero)) v∷ vNil))
  ≡ satFormula (T₁ v∷ vNil)
      (((σ₊ , fzero) , (σ₋ , fzero)
          , (σ₊ , fzero)) v∷ vNil)
Cnf-check-of3-sat = refl

-- 公式账 = 全部文字数（3-CNF 一条 3-子句 ⟹ 3 步，与 SATMember 的 3/子句相容）
Cnf-check-steps-of3 :
  steps (satFormula'C (T₁ v∷ vNil)
           (formulaOf3 (((σ₊ , fzero) , (σ₋ , fzero)
                           , (σ₊ , fzero)) v∷ vNil)))
  ≡ 3
Cnf-check-steps-of3 = refl

-- ────────────────────────────────────────────────────────────────────
-- §6 尾注立界（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)  本件只给「一般 CNF 的类型 + 语义 + 拼接 + 计账 + 3-CNF 嵌入」。
--      **Tseitin（长子句 ⟹ 等可满足的 3-子句组）在 CNF-Tseitin.agda**（M1b），
--      本件不含辅助变量、不做范式转换链（命题逻辑规范化不是 CL 所需）。
-- (ii) 未与 `InNP` 接线：本层是「公式」而不是「语言」，M2 才加 `InNP-TM`。
-- (iii) `Formula'` 用 List（无长度索引）⟹ 公式的「规模」只能事后用
--      `length (concat φ)` 表述；这是有意的（见头注「为什么用 List」）。
-- (iv) 空子句 = false 是**语义选择**（空析取），不是遗漏：它使 `[] ∷ φ` 恒假，
--      正是「该公式不可满足」；`satFormula'-cons-false` 把这条钉死。

-- 0 postulate / 0 hole。
