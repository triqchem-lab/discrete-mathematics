{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Foundation.FMTK
-- 有限模型论 k 变元泛化（FTK）——PvsNP 批三，Fagin 链（NP=ESO）前置工程
--
-- 定位：FMT（Foundation.FiniteModelTheory）的双变元片段（Var = Fin 2 硬编码）
--   升为 k 变元参数化。**FO 片段口径不变，仅变元域 k 参数化**：语法仍是
--   关系原子（≤2 元关系词汇保持）/ ¬ / ∧ / ∨ / 逐变元存在量化——量化仍逐
--   变元 existential（∃-over-Fin n 的语义枚举，非语法绑定），与旧件同范式。
--   相对旧件的唯一语法增量：等式原子 FTK-atomEq——「k 元两两不等式组」的
--   最低限必需件（旧件 §4 自承「双变元片段不足以表达」AtLeast-k 公式形）。
--
--   本件是 Fagin 链（NP=ESO）的前置：k 变元承载就位后，ESO 层（二阶存在
--   量词语义，~300 行）才有挂靠面；Fagin 定理本体维持 W2 立界不排期。
--
-- 分级标注：〔结构定义〕〔结构证明〕〔核对〕〔立界注记〕（同库惯例）。
-- 0 postulate / 0 hole。

module Sovereign.Foundation.FMTK where

open import Data.List using (List; []; _∷_; map)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc; pred)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import Sovereign.Foundation.FiniteModelTheory as FMT

-- ────────────────────────────────────────────────────────────────────
-- §1 FTK-Formula k：k 变元 FO 片段〔结构定义〕
-- ────────────────────────────────────────────────────────────────────
-- 变元域 = Fin k；语法与旧件同范式泛化，关系词汇保持（R₁ 一元 + S₂ 二元），
-- 等式原子为唯一增量（§4 两两不等式组的必需件）。

data FTK-Formula (k : ℕ) : Set where
  FTK-atomR  : Fin k → FTK-Formula k                  -- R x（一元，词汇保持）
  FTK-atomS  : Fin k → Fin k → FTK-Formula k          -- S x y（二元，词汇保持）
  FTK-atomEq : Fin k → Fin k → FTK-Formula k          -- x ≡ y（增量：AtLeast-k 必需）
  FTK-bot    : FTK-Formula k
  FTK-neg    : FTK-Formula k → FTK-Formula k
  FTK-or     : FTK-Formula k → FTK-Formula k → FTK-Formula k
  FTK-and    : FTK-Formula k → FTK-Formula k → FTK-Formula k
  FTK-ex     : Fin k → FTK-Formula k → FTK-Formula k  -- 逐变元 ∃（语义枚举，非语法绑定）

-- ────────────────────────────────────────────────────────────────────
-- §2 FTK-varEq：泛型变元相等判定〔结构证明〕
-- ────────────────────────────────────────────────────────────────────
-- 类型面：Fin k 单射性（toℕ 相等 ⟹ 相等，3 行归纳）；判定面：旧 varEq
-- （双变元逐点穷举）的结构递归泛型形；语义面：赋值 ρ 下 x ≡ y ⟺ ρ x ≡ ρ y
-- 的判定器及其双向正确性（等式原子的语义挂靠件，§3 消费）。

-- Fin k 单射性（类型面）
FTK-toℕ-inj : ∀ {k : ℕ} (i j : Fin k) → toℕ i ≡ toℕ j → i ≡ j
FTK-toℕ-inj fzero    fzero    _ = refl
FTK-toℕ-inj fzero    (fsuc _) ()
FTK-toℕ-inj (fsuc _) fzero    ()
FTK-toℕ-inj (fsuc i) (fsuc j) p = cong fsuc (FTK-toℕ-inj i j (cong pred p))

-- 判定器（语法面）：Fin k 结构递归——旧件 varEq 的泛型形
FTK-varEq : ∀ {k : ℕ} (x y : Fin k) → Bool
FTK-varEq fzero    fzero    = true
FTK-varEq fzero    (fsuc _) = false
FTK-varEq (fsuc _) fzero    = false
FTK-varEq (fsuc x) (fsuc y) = FTK-varEq x y

FTK-varEq-refl : ∀ {k : ℕ} (x : Fin k) → FTK-varEq x x ≡ true
FTK-varEq-refl fzero    = refl
FTK-varEq-refl (fsuc x) = FTK-varEq-refl x

FTK-varEq-sound : ∀ {k : ℕ} (x y : Fin k) → x ≡ y → FTK-varEq x y ≡ true
FTK-varEq-sound x .x refl = FTK-varEq-refl x

FTK-varEq-complete : ∀ {k : ℕ} (x y : Fin k) → FTK-varEq x y ≡ true → x ≡ y
FTK-varEq-complete fzero    fzero    _ = refl
FTK-varEq-complete fzero    (fsuc _) ()
FTK-varEq-complete (fsuc _) fzero    ()
FTK-varEq-complete (fsuc x) (fsuc y) p = cong fsuc (FTK-varEq-complete x y p)

-- 语义侧判定器：赋值 ρ 下 x ≡ y ⟺ ρ x ≡ ρ y
FTK-ρeq : ∀ {n k : ℕ} (ρ : Fin k → Fin n) (x y : Fin k) → Bool
FTK-ρeq ρ x y = FTK-varEq (ρ x) (ρ y)

FTK-ρeq-sound : ∀ {n k : ℕ} (ρ : Fin k → Fin n) (x y : Fin k) →
  ρ x ≡ ρ y → FTK-ρeq ρ x y ≡ true
FTK-ρeq-sound ρ x y p = FTK-varEq-sound (ρ x) (ρ y) p

FTK-ρeq-complete : ∀ {n k : ℕ} (ρ : Fin k → Fin n) (x y : Fin k) →
  FTK-ρeq ρ x y ≡ true → ρ x ≡ ρ y
FTK-ρeq-complete ρ x y p = FTK-varEq-complete (ρ x) (ρ y) p

-- ────────────────────────────────────────────────────────────────────
-- §3 FTK-evalF：泛型求值器〔结构定义〕（Bool 通道，与旧件同范式）
-- ────────────────────────────────────────────────────────────────────
-- 结构域与旧件口径一致：载体 Fin n（Structure 承载解释函数族 R₁/S₂，
-- 与旧件共用同一 record）；赋值泛化为 Fin k → Fin n。

-- 赋值：k 变元 → 载体 Fin n
FTK-Env : ℕ → ℕ → Set
FTK-Env n k = Fin k → Fin n

-- 环境扩展（免 mixfix——旧件同款 where-布尔分流）
FTK-extend : ∀ {n k : ℕ} → FTK-Env n k → Fin k → Fin n → FTK-Env n k
FTK-extend ρ x v y = h (FTK-varEq x y)
  where
  h : Bool → Fin _
  h true  = v
  h false = ρ y

-- ∃ 沿 Fin n 枚举（旧件 anyOf 的泛型形）
FTK-anyOf : ∀ {n : ℕ} → (Fin n → Bool) → Bool
FTK-anyOf {zero}  f = false
FTK-anyOf {suc n} f = f fzero ∨ FTK-anyOf {n} (λ i → f (fsuc i))

-- 泛型求值器：关系原子走解释函数族，等式原子走 FTK-ρeq 判定器，
-- ∃ 逐变元沿 Fin n 语义枚举
FTK-evalF : ∀ {n k : ℕ} → FMT.Structure n → FTK-Env n k → FTK-Formula k → Bool
FTK-evalF M ρ (FTK-atomR x)    = FMT.Structure.R₁ M (ρ x)
FTK-evalF M ρ (FTK-atomS x y)  = FMT.Structure.S₂ M (ρ x) (ρ y)
FTK-evalF M ρ (FTK-atomEq x y) = FTK-ρeq ρ x y
FTK-evalF M ρ FTK-bot          = false
FTK-evalF M ρ (FTK-neg φ)      = not (FTK-evalF M ρ φ)
FTK-evalF M ρ (FTK-or φ ψ)     = FTK-evalF M ρ φ ∨ FTK-evalF M ρ ψ
FTK-evalF M ρ (FTK-and φ ψ)    = FTK-evalF M ρ φ ∧ FTK-evalF M ρ ψ
FTK-evalF M ρ (FTK-ex x φ)     = FTK-anyOf (λ v → FTK-evalF M (FTK-extend ρ x v) φ)

-- ────────────────────────────────────────────────────────────────────
-- §4 FTK-AtLeast k：k 变元两两不等式组〔结构定义〕
-- ────────────────────────────────────────────────────────────────────
-- 旧件 §4 的 AtLeast 是「载体规模声明」（Σ n, k ≤ n），自承双变元片段不足以
-- 公式化；k 变元面下它升为 FO 公式形：∃x₀ … ∃x_{k-1} ∧_{i<j} ¬(xᵢ ≡ xⱼ)。

-- Fin k 全变元表
FTK-fins : (k : ℕ) → List (Fin k)
FTK-fins zero    = []
FTK-fins (suc k) = fzero ∷ map fsuc (FTK-fins k)

-- ⊤ 基座（语法无 ⊤：¬⊥ 承担空合取单位）
FTK-top : ∀ {k : ℕ} → FTK-Formula k
FTK-top = FTK-neg FTK-bot

-- x 对尾表逐元不等
FTK-allNeq : ∀ {k : ℕ} → Fin k → List (Fin k) → FTK-Formula k
FTK-allNeq x []       = FTK-top
FTK-allNeq x (y ∷ ys) = FTK-and (FTK-neg (FTK-atomEq x y)) (FTK-allNeq x ys)

-- 两两不等式组：首变元对其余 + 余元递归（严格对 (i,j), i<j 恰一遍）
FTK-pwStep : ∀ {k : ℕ} → List (Fin k) → FTK-Formula k
FTK-pwStep []       = FTK-top
FTK-pwStep (x ∷ xs) = FTK-and (FTK-allNeq x xs) (FTK-pwStep xs)

FTK-pairwiseNeq : (k : ℕ) → FTK-Formula k
FTK-pairwiseNeq k = FTK-pwStep (FTK-fins k)

-- k 折 ∃ 封包（按全变元表逐变元量化）
FTK-exBlock : ∀ {k : ℕ} → List (Fin k) → FTK-Formula k → FTK-Formula k
FTK-exBlock []       φ = φ
FTK-exBlock (x ∷ xs) φ = FTK-ex x (FTK-exBlock xs φ)

-- AtLeast k 公式形：∃x₀ … ∃x_{k-1} 两两不等
FTK-AtLeast : (k : ℕ) → FTK-Formula k
FTK-AtLeast k = FTK-exBlock (FTK-fins k) (FTK-pairwiseNeq k)

-- ────────────────────────────────────────────────────────────────────
-- §5 核对层〔核对〕
-- ────────────────────────────────────────────────────────────────────
-- 5.1 k=2 一致性：旧 Formula → FTK-Formula 2 的升格映射 + 样例公式上
--     新旧求值器一致性（refl——两侧归约同形：FTK-varEq/FTK-anyOf/FTK-extend
--     与旧 varEq/anyOf/extend 逐条同款）。

FTK-up2 : FMT.Formula → FTK-Formula 2
FTK-up2 (FMT.atomR x)   = FTK-atomR x
FTK-up2 (FMT.atomS x y) = FTK-atomS x y
FTK-up2 FMT.⊥ᶠ          = FTK-bot
FTK-up2 (FMT.¬ᶠ φ)      = FTK-neg (FTK-up2 φ)
FTK-up2 (FMT.∨ᶠ φ ψ)    = FTK-or (FTK-up2 φ) (FTK-up2 ψ)
FTK-up2 (FMT.∧ᶠ φ ψ)    = FTK-and (FTK-up2 φ) (FTK-up2 ψ)
FTK-up2 (FMT.∃ᶠ x φ)    = FTK-ex x (FTK-up2 φ)

-- 核对⑤：∃ 样例公式在任意 2 元结构/赋值上与旧 evalF 一致
FTK-cons-∃ : ∀ (M : FMT.Structure 2) (ρ : FMT.Env 2) →
  FTK-evalF M ρ (FTK-up2 (FMT.∃ᶠ fzero (FMT.atomS fzero (fsuc fzero))))
  ≡ FMT.evalF M ρ (FMT.∃ᶠ fzero (FMT.atomS fzero (fsuc fzero)))
FTK-cons-∃ M ρ = refl

-- 核对⑥：命题复合样例公式（¬ ∨ ⊥ + S 原子）同上（∨ᶠ 为前缀标识符）
FTK-cons-logic : ∀ (M : FMT.Structure 2) (ρ : FMT.Env 2) →
  FTK-evalF M ρ (FTK-up2 (FMT.¬ᶠ (FMT.∨ᶠ FMT.⊥ᶠ (FMT.atomS fzero (fsuc fzero)))))
  ≡ FMT.evalF M ρ (FMT.¬ᶠ (FMT.∨ᶠ FMT.⊥ᶠ (FMT.atomS fzero (fsuc fzero))))
FTK-cons-logic M ρ = refl

-- 5.2 k=3 对照实例：AtLeast 3 在 3 元结构可满足 / 2 元结构不可满足
--     （鸽笼——旧件「规模声明」面没有的语义锚，此处以闭式计算 refl 锚定）

FTK-M3 : FMT.Structure 3
FTK-M3 = record { R₁ = λ _ → true ; S₂ = λ _ _ → true }

FTK-ρ3 : FTK-Env 3 3
FTK-ρ3 = λ _ → fzero

FTK-ρ23 : FTK-Env 2 3
FTK-ρ23 = λ _ → fzero

-- 核对⑦：3 元结构 ⊨ AtLeast 3
FTK-check-AtLeast3-yes : FTK-evalF FTK-M3 FTK-ρ3 (FTK-AtLeast 3) ≡ true
FTK-check-AtLeast3-yes = refl

-- 核对⑧：2 元结构 ⊭ AtLeast 3（8 分支逐案闭式计算归 false）
FTK-check-AtLeast3-no : FTK-evalF FMT.M2 FTK-ρ23 (FTK-AtLeast 3) ≡ false
FTK-check-AtLeast3-no = refl

-- ────────────────────────────────────────────────────────────────────
-- §6 尾注：立界清单（诚实边界——不设空壳签名）〔立界注记〕
-- ────────────────────────────────────────────────────────────────────
-- (i)  句法闭包证书：FTK-AtLeast k 经 FTK-exBlock 全变元量化后类型仍是
--      FTK-Formula k——「句子」在此是语义事实（FTK-fins k 覆盖全部变元），
--      类型级句子证书（Formula 0 挂靠）需 index-weakening / de Bruijn
--      机器，随 ESO 层需要再立，本件不闭合。
-- (ii) ESO 层（二阶存在量词语义，~300 行）——Fagin 链下一环；k 变元公式 +
--      Bool 求值通道（本件）即其挂靠面，未排期。
-- (iii) Fagin 定理本体（NP=ESO）——W2 立界不排期，本件不触碰。
-- (iv) 紧致性失效严格证明 / Trakhtenbrot / 0-1 律——沿用旧件 §5 深件立界。
-- (v)  FTK-up2 是 k=2 的全语法升格；一般 k ≤ 2 弱化映射（weakening）随用
--      随立。

-- 0 postulate / 0 hole。
-- 本文件由 agda +RTS -M8G -H6G -A128M -RTS 编译，EXIT=0 为完成判据。
