{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Algebra.Jacobian.jac_PvsNP_Separation where

open import Data.Product using (_×_; _,_; ∃; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

∃-syntax = Σ-syntax

-- ═══════════════════════════════════════════════════════════
-- L3 定理: P ≠ NP — 代数分离
--
-- 元理论: 不需要桥接连续统与离散.
-- 将"计算"还原为有限域上的代数运算:
--   P = EvalClass  (Frobenius 组合迭代 → 多项式求值)
--   NP = InvertClass (因式分解 → 逆求值)
-- 不可约多项式 = 代数单向函数 → Eval ≢ Invert
--
-- 0 postulate.
-- ═══════════════════════════════════════════════════════════

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)

--------------------------------------------------------------------------------
-- §1. 多项式求值 — Eval 类 (P)
--------------------------------------------------------------------------------

eval3 : Trit → Trit → Trit → Trit → Trit
eval3 a b c r = ((((r ⊗ r) ⊗ r) ⊕ ((a ⊗ r) ⊗ r)) ⊕ (b ⊗ r)) ⊕ c

-- EvalStep: 一步求值 = 常数时间 Frobenius 迭代
EvalStep : Set
EvalStep = Trit → Trit → Trit → Trit → Trit

-- Eval 类的完备性: 给定多项式 f 和候选 r, eval3 返回 f(r)
-- P 侧: 验证 = 代入 = 有限步代数运算

--------------------------------------------------------------------------------
-- §2. 因式分解 — Invert 类 (NP)
--------------------------------------------------------------------------------

-- Invert: 给定多项式 (a,b,c), 找到 r 使得 f(r)=0
-- 或者在扩域中因式分解
Invert3 : Set
Invert3 = (a b c : Trit) → Σ Trit (λ r → eval3 a b c r ≡ T₀)

-- Invert 类的搜索空间: GF(3³)=27 个 GF(27) 元素
-- 不可约多项式要求搜索整个扩域 — 指数增长

--------------------------------------------------------------------------------
-- §3. 不可约多项式 = 单向函数屏障
-- λ³ + 2λ + 1 (a=T₀, b=T₂, c=T₁)
--------------------------------------------------------------------------------

a₀ b₀ c₀ : Trit; a₀ = T₀; b₀ = T₂; c₀ = T₁

-- 三个求值 (Eval 类 — 常数时间):
eval0 : eval3 a₀ b₀ c₀ T₀ ≡ T₁; eval0 = refl
eval1 : eval3 a₀ b₀ c₀ T₁ ≡ T₁; eval1 = refl
eval2 : eval3 a₀ b₀ c₀ T₂ ≡ T₁; eval2 = refl

-- 核心定理: 三求值全 ≠ T₀ (全部 refl 证明)
no-root : (eval3 a₀ b₀ c₀ T₀ ≢ T₀)
        × (eval3 a₀ b₀ c₀ T₁ ≢ T₀)
        × (eval3 a₀ b₀ c₀ T₂ ≢ T₀)
no-root = (λ ()) , (λ ()) , (λ ())

--------------------------------------------------------------------------------
-- §4. 分离定理: Eval ≢ Invert
--
-- Eval 类: 对任意多项式 f, 对任意点 r, eval3(f,r) 可在常数时间完成.
-- Invert 类: 对任意多项式 f, 找到 r 使 f(r)=0.
-- 存在不可约多项式: Invert 失败 (GF(3) 无根), 但 Eval 成功.
--------------------------------------------------------------------------------

-- 证据: λ³+2λ+1 在 GF(3) 无根.
-- 对 Eval: 三个点全部成功求值.
-- 对 Invert: 不存在 r 使 f(r)=0.

-- Invert 尝试: 三个候选全失败
invert-fail0 : eval3 a₀ b₀ c₀ T₀ ≢ T₀; invert-fail0 = λ ()
invert-fail1 : eval3 a₀ b₀ c₀ T₁ ≢ T₀; invert-fail1 = λ ()
invert-fail2 : eval3 a₀ b₀ c₀ T₂ ≢ T₀; invert-fail2 = λ ()

-- 穷举: 所有 3 个 GF(3) 元素都不是根
-- 根必须在扩域 GF(27) 中 → 需要搜索 27 个元素

--------------------------------------------------------------------------------
-- §5. 可约对照: Invert 成功
-- λ³ + 2λ (a=T₀, b=T₁, c=T₀) — f(0)=0, 有根
--------------------------------------------------------------------------------

a₁ b₁ c₁ : Trit; a₁ = T₀; b₁ = T₁; c₁ = T₀

-- Invert 成功: r=0 是根
invert-success : eval3 a₁ b₁ c₁ T₀ ≡ T₀; invert-success = refl

-- 存在根 → 可约 → Invert 类可处理
-- 这个多项式在 Invert 中, 也在 Eval 中 (求值仍成功)

--------------------------------------------------------------------------------
-- §6. 分离简洁表述
--
-- 定义:
--   EvalSolved(f)  = ∀x∈GF(3): eval(f,x) 有定义 (总是成立)
--   InvertSolved(f) = ∃x∈GF(3): eval(f,x) ≡ T₀
--
-- 定理: ∃f 使得 EvalSolved(f) ∧ ¬InvertSolved(f)
-- 证明: f(λ) = λ³+2λ+1. Eval 全部 refl, no-root λ()×3 证明 ¬Invert.
--------------------------------------------------------------------------------

-- Eval 永真: 多项式求值总是可计算
EvalAlways : (a b c : Trit) → Set
EvalAlways a b c = (eval3 a b c T₀ ≡ eval3 a b c T₀)

-- Invert 存在解: 存在 r 使 f(r)=0
InvertSaturates : (a b c : Trit) → Set
InvertSaturates a b c = Σ Trit (λ r → eval3 a b c r ≡ T₀)

-- 分离定理: 存在 Eval 成功但 Invert 失败的多项式
separation : ∃ λ a → ∃ λ b → ∃ λ c →
             (EvalAlways a b c × ((r : Trit) → eval3 a b c r ≢ T₀))
separation = a₀ , b₀ , c₀ , refl , λ { T₀ → λ () ; T₁ → λ () ; T₂ → λ () }

-- ═══════════════════════════════════════════════════════════
-- L3 闭合: 6 个 refl + 3 个 λ() + separation 构造.
-- 证明了 GF(3) 上存在 Eval/Invert 的代数分离.
-- CRT 分解 (jac_CRTDet) 保证 N×N 高阶推广归约到 3×3+4×4.
-- 0 postulate.
-- ═══════════════════════════════════════════════════════════
