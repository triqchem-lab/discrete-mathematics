{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Fermat.FermatL0
-- 费马大定理的离散基座 — L0 定义层
--
-- 数学背景:
--   费马大定理 (FLT): aⁿ+bⁿ=cⁿ (n≥3) 无正整数解 — 经典 Wiles 证明 (连续统序结构).
--   本框架裁决 (docs/duodecimal/13-flt-analysis.md):
--     "无解性不在幂的律里, 在 Archimedes 序的债务里."
--   本目录按 L0→L3 阶段推进, 把 FLT 的"幂的律"部分在 GF(3)×GF(9) 离散基座上
--   完整形式化: 幂周期坍缩 (周期 2 与周期 8) 是可穷举判定的代数事实.
--
-- L0 (本模块): 定义层
--   - pow3 : GF(3) 上的幂函数 (x⁰ = 1 约定)
--   - 零幂族: 0^(n+1) = 0 (零是唯一跨维度元素, 见 04-zero-oblivion)
--   - 单位幂: 1ⁿ = 1
--   - GF(3)× 分类: 非零元 = {T₁, T₂}
--   - 局部不等号 _≢₃_ (GF9.agda 惯例: 模块内定义, 避免污染全局记法)
--
-- 0 postulate.

module Sovereign.Problem.Fermat.FermatL0 where

open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; module ≡-Reasoning)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊗_; _⊕_; ⊗-identityˡ; ⊗-zeroˡ)

--------------------------------------------------------------------------------
-- §1. GF(3) 上的不等号 (局部)
--------------------------------------------------------------------------------

_≢₃_ : Trit → Trit → Set
x ≢₃ y = x ≡ y → ⊥

-- 构造子不相交: T₀ ≢ T₁ 等由 λ() 自动成立 (data 无冲突)

--------------------------------------------------------------------------------
-- §2. GF(3) 幂函数
--------------------------------------------------------------------------------

-- xⁿ: 约定 x⁰ = 1 (乘法单位元)
pow3 : Trit → ℕ → Trit
pow3 x zero = T₁
pow3 x (suc n) = x ⊗ pow3 x n

-- 展开引理: x^(n+1) = x ⊗ xⁿ (定义等式, refl)
pow3-expand : ∀ x n → pow3 x (suc n) ≡ x ⊗ pow3 x n
pow3-expand x n = refl

--------------------------------------------------------------------------------
-- §3. 零幂族: 0^(n+1) = 0
--
-- 零是唯一跨维度的元素: 0ⁿ = 0 对所有 n ≥ 1.
-- 此即 GF(9) 出生证明 1²+α²=0² 中 0² 的零幂族语义 (10-norm-collapse §1).
-- 对照: 勾股/FLT 幂等式的"零通道" (13-flt-analysis §3.3, §10) 由此层奠基.
--------------------------------------------------------------------------------

pow3-zero-suc : ∀ n → pow3 T₀ (suc n) ≡ T₀
pow3-zero-suc n = refl   -- 归约: T₀ ⊗ pow3 T₀ n → T₀ (⊗-zeroˡ)

-- 0 的偶次幂 (正): 0^(2k) = 0 当 2k ≥ 1
pow3-zero-even : ∀ n → pow3 T₀ (suc (n * 2)) ≡ T₀
pow3-zero-even n = refl

-- 0 的奇次幂 (正): 0^(2k+1) = 0
pow3-zero-odd : ∀ n → pow3 T₀ (suc (suc (n * 2))) ≡ T₀
pow3-zero-odd n = refl

--------------------------------------------------------------------------------
-- §4. 单位幂: 1ⁿ = 1
--------------------------------------------------------------------------------

pow3-one : ∀ n → pow3 T₁ n ≡ T₁
pow3-one zero = refl
pow3-one (suc n) = trans (⊗-identityˡ (pow3 T₁ n)) (pow3-one n)
  -- pow3 T₁ (suc n) = T₁ ⊗ pow3 T₁ n ≡[⊗-identityˡ] pow3 T₁ n ≡[IH] T₁

--------------------------------------------------------------------------------
-- §5. GF(3)× 分类: 非零元恰为 {T₁, T₂}
--------------------------------------------------------------------------------

-- 三分: 每个元素恰为 T₀ / T₁ / T₂ 之一
trit-class : ∀ x → x ≡ T₀ ⊎ x ≡ T₁ ⊎ x ≡ T₂
trit-class T₀ = inj₁ refl
trit-class T₁ = inj₂ (inj₁ refl)
trit-class T₂ = inj₂ (inj₂ refl)

-- 非零分类: x ≢ T₀ → x ≡ T₁ ⊎ x ≡ T₂
nonzero-class : ∀ x → x ≢₃ T₀ → x ≡ T₁ ⊎ x ≡ T₂
nonzero-class T₀ neq = ⊥-elim (neq refl)
nonzero-class T₁ _   = inj₁ refl
nonzero-class T₂ _   = inj₂ refl

-- 零判定 (L2 零通道定理的支柱): 每个元素要么是零要么非零
zero-trit? : ∀ w → w ≡ T₀ ⊎ w ≢₃ T₀
zero-trit? T₀ = inj₁ refl
zero-trit? T₁ = inj₂ (λ ())
zero-trit? T₂ = inj₂ (λ ())

--------------------------------------------------------------------------------
-- §6. T₂ 幂实例表 (可计算性展示, 全部 refl)
--------------------------------------------------------------------------------

-- 2⁰ = 1, 2¹ = 2, 2² = 1, 2³ = 2, 2⁴ = 1 (周期 2 已现雏形)
pow3-T2-0 : pow3 T₂ 0 ≡ T₁ ; pow3-T2-0 = refl
pow3-T2-1 : pow3 T₂ 1 ≡ T₂ ; pow3-T2-1 = refl
pow3-T2-2 : pow3 T₂ 2 ≡ T₁ ; pow3-T2-2 = refl
pow3-T2-3 : pow3 T₂ 3 ≡ T₂ ; pow3-T2-3 = refl
pow3-T2-4 : pow3 T₂ 4 ≡ T₁ ; pow3-T2-4 = refl
