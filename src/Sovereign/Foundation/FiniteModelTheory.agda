{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Foundation.FiniteModelTheory
-- 有限模型论——离散数学基础任务池 P3 尾批（深件设计先行）
--
-- 数学背景：有限模型论研究「仅限有限结构」的一阶逻辑面——与经典模型论的
--   关键分野：**紧致性定理失效**（句子族 {≥n : n∈ℕ} 有限可满足而整体在有限
--   结构类中不可满足）；Trakhtenbrot 定理（有限可满足性不可判定）。
--   有限结构 = 载体 Fin n + 关系解释；满足关系 = Tarski 递归（Bool 通道可计算形）。
--
-- 核心原则：
-- 1. 关系入定义：Structure record 承载载体+关系解释（零外来公理）；
-- 2. 公式层用**双变元片段**（Var = Fin 2）——够立界例与紧致性反例面；
--    一般变元集/函数符号/等式原子随立界；
-- 3. 满足语义 evalF 走 Bool 通道（可计算形——与 PropositionalLogic.evalF 同范式）；
-- 4. ⚠ 诚实边界：**紧致性失效严格证明/Trakhtenbrot/0-1 律 = 深件**——立界注记。
--
-- 包含：Structure · Formula（双变元 FO 片段）· evalF · 二元素结构实例
--       · 紧致性反例句族（≥n 形声明面）· 核对层 · 深件立界

module Sovereign.Foundation.FiniteModelTheory where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ────────────────────────────────────────────────────────────────────
-- §1 定义层（有限结构——关系入定义）
-- ────────────────────────────────────────────────────────────────────

-- 有限结构（二元关系词汇表：R 一元 + S 二元——够紧致性反例/小例面）
record Structure (n : ℕ) : Set where
  field
    R₁ : Fin n → Bool          -- 一元关系解释
    S₂ : Fin n → Fin n → Bool  -- 二元关系解释

-- 变元（双变元片段）
Var : Set
Var = Fin 2

-- 公式（双变元 FO 片段：原子 + 命题联结 + ∃）
data Formula : Set where
  atomR : Var → Formula                -- R x
  atomS : Var → Var → Formula          -- S x y
  ⊥ᶠ    : Formula
  ¬ᶠ    : Formula → Formula
  ∨ᶠ    : Formula → Formula → Formula
  ∧ᶠ    : Formula → Formula → Formula
  ∃ᶠ    : Var → Formula → Formula      -- ∃ 变元量化

-- 环境（变元赋值）
Env : (n : ℕ) → Set
Env n = Var → Fin n

-- 环境扩展（免 mixfix——运算符段式不可靠教训预采纳）
varEq : Var → Var → Bool
varEq fzero fzero         = true
varEq fzero (fsuc _)      = false
varEq (fsuc _) fzero      = false
varEq (fsuc fzero) (fsuc fzero) = true
varEq (fsuc fzero) (fsuc (fsuc ())) 
varEq (fsuc (fsuc ()))    _

extend : {n : ℕ} → Env n → Var → Fin n → Env n
extend ρ x v y = g (varEq x y)
  where
  g : Bool → Fin _
  g true  = v
  g false = ρ y

-- ────────────────────────────────────────────────────────────────────
-- §2 满足语义（Bool 通道——可计算形，与 evalF 同范式）
-- ────────────────────────────────────────────────────────────────────

-- ∃ 沿 Fin n 枚举（辅助递归）
anyOf : {n : ℕ} → (Fin n → Bool) → Bool
anyOf {zero}  f = false
anyOf {suc n} f = f fzero ∨ anyOf {n} (λ i → f (fsuc i))

evalF : {n : ℕ} → Structure n → Env n → Formula → Bool
evalF M ρ (atomR x)   = Structure.R₁ M (ρ x)
evalF M ρ (atomS x y) = Structure.S₂ M (ρ x) (ρ y)
evalF M ρ ⊥ᶠ          = false
evalF M ρ (¬ᶠ φ)      = not (evalF M ρ φ)
evalF M ρ (∨ᶠ φ ψ)    = evalF M ρ φ ∨ evalF M ρ ψ
evalF M ρ (∧ᶠ φ ψ)    = evalF M ρ φ ∧ evalF M ρ ψ
evalF M ρ (∃ᶠ x φ)    = anyOf (λ v → evalF M (extend ρ x v) φ)


-- ────────────────────────────────────────────────────────────────────
-- §3 二元素结构实例与核对层
-- ────────────────────────────────────────────────────────────────────

-- 二元素全真结构（R₁≡true / S₂≡true）
M2 : Structure 2
M2 = record { R₁ = λ _ → true ; S₂ = λ _ _ → true }

ρ0 : Env 2
ρ0 = λ _ → fzero

-- 核对①：全真结构上 R x 恒真
check-R : evalF M2 ρ0 (atomR fzero) ≡ true
check-R = refl

-- 核对②：∃x S x y 恒真（全真面——anyOf 首项即 true）
check-exists : evalF M2 ρ0 (∃ᶠ fzero (atomS fzero fzero)) ≡ true
check-exists = refl

-- 核对③：⊥ 恒假
check-bot : evalF M2 ρ0 ⊥ᶠ ≡ false
check-bot = refl

-- 核对④：¬⊥ 恒真
check-notbot : evalF M2 ρ0 (¬ᶠ ⊥ᶠ) ≡ true
check-notbot = refl

-- ────────────────────────────────────────────────────────────────────
-- §4 紧致性反例句族（声明面——有限版紧致性失效的构造锚）
-- ────────────────────────────────────────────────────────────────────
-- 句子「≥k」：存在 k 个两两不等元素（有限结构语境：载体 ≥ k）。
-- 族 {≥k : k ∈ ℕ} 任意有限子族在足够大有限结构中可满足；
-- 整体在**有限结构类**中无模型——紧致性失效的反例族（严格证明=深件立界）。
-- 注：本层以「载体规模条件」直陈（不展开「两两不等」公式形——
--     双变元片段不足以表达 k 元不等式组，需 k 变元面=立界 (ii)）。

_≤?_ : ℕ → ℕ → Bool
zero  ≤? _     = true
suc _ ≤? zero  = false
suc m ≤? suc n = m ≤? n

-- AtLeast k = 存在载体规模 n ≥ k（紧致性反例族的锚）
AtLeast : ℕ → Set
AtLeast k = Σ[ n ∈ ℕ ] ((k ≤? n) ≡ true)

-- ────────────────────────────────────────────────────────────────────
-- §5 深件立界（诚实边界——不设空壳签名）
-- ────────────────────────────────────────────────────────────────────
-- (i)   紧致性失效严格证明（反例族完备形）——独立批 150-250；
-- (ii)  k 变元面（k 元不等式组的公式形——双变元片段外延）；
-- (iii) Trakhtenbrot 定理（有限可满足性不可判定）——深件 300+ 诚实界；
-- (iv)  0-1 律（Fagin/渐进性）——深件；
-- (v)   与 PropositionalLogic（2b7e413a）满足语义的衔接对齐注记。
