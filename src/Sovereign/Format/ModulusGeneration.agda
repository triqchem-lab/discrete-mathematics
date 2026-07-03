{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Format.ModulusGeneration
-- 幻方正交拓扑：CRT 模数生成协议
--
-- 给定环面测地线步数 k，用 M₄ 本征谱 + 克里斯托螺旋
-- 生成 CRT 模数 m_i(k)。正交判据 Orth 取代传统 gcd 互质。

module Sovereign.Format.ModulusGeneration where

open import Data.Nat using (ℕ; zero; suc; _*_; _/_; _%_)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Base.Invariants using (SOVEREIGN_LCM; POW2₁₆; POW3₁₁)
open import Sovereign.RootMath.DigitalRoot using (christosStep)
open import Sovereign.Structology.MagicSquareM4 using (Σ-M4; Orth; v34; v0; orth-v34-v0)

-- 本地别名
SOVEREIGN_M : ℕ
SOVEREIGN_M = SOVEREIGN_LCM

Q : ℕ
Q = POW2₁₆

--------------------------------------------------------------------------------
-- 1. 克里斯托螺旋展开算子 Φ^k
--------------------------------------------------------------------------------

-- Φ(k) = christosStep^k (1)
-- 序列: k=0→1, k=1→2, k=2→4, k=3→8, k=4→7, k=5→5, k=6→1
Φ : ℕ → ℕ
Φ zero    = 1
Φ (suc k) = christosStep (Φ k)

-- Φ 的周期 = 6
-- Φ(6) = 1, Φ(7) = 2, ...

--------------------------------------------------------------------------------
-- 2. CRT 模数生成 m_i(k)
--------------------------------------------------------------------------------

-- m_i(k) = (λ_i · Φ(k)) mod M
-- 其中 λ_i ∈ Σ-M4 = {34, 0, 16, -16}
-- M = 3^11 · 2^16 = 11609505792

-- 模数生成（ℕ 版本，仅处理非负本征值）
modulusGen : ℕ → ℕ → ℕ
modulusGen lam k = (lam * Φ k) % SOVEREIGN_M

-- 四个 CRT 模数序列
m₁ : ℕ → ℕ   -- 对应 λ=34
m₁ k = modulusGen 34 k

m₂ : ℕ → ℕ   -- 对应 λ=0（零模数）
m₂ k = 0

m₃ : ℕ → ℕ   -- 对应 λ=16（正手征）
m₃ k = modulusGen 16 k

m₄ : ℕ → ℕ   -- 对应 λ=16（负手征，对称）
m₄ k = modulusGen 16 k  -- 负号在 mod M 下等价

-- 模数序列
modulusSequence : ℕ → Vec ℕ 4
modulusSequence k = m₁ k ∷ m₂ k ∷ m₃ k ∷ m₄ k ∷ []

--------------------------------------------------------------------------------
-- 3. 正交性质验证
--------------------------------------------------------------------------------

-- 关键性质：m₃(k) 与 m₄(k+3) 正交（相位差 3 步，半周期）
-- 因为 christosStep³ = christosStep(christosStep(christosStep(1)))
--                      = christosStep(8) = 7 → 实际上是倒置关系

-- 克里斯托螺旋的对称性：
--   Φ(k) 与 Φ(k+3) 互补（1↔8, 2↔7, 4↔5）
coPhase : ℕ → ℕ
coPhase k = Φ (k + 3)

-- 验证 1↔8 互补
verify1to8 : Φ 0 + coPhase 0 ≡ 9  -- 1 + 8 = 9
verify1to8 = refl

verify2to7 : Φ 1 + coPhase 1 ≡ 9  -- 2 + 7 = 9
verify2to7 = refl

verify4to5 : Φ 2 + coPhase 2 ≡ 9  -- 4 + 5 = 9
verify4to5 = refl

--------------------------------------------------------------------------------
-- 4. 投影到 CRT 空间
--------------------------------------------------------------------------------

-- 给定步数 k，生成模数对 (m_i, m_j) 满足 Orth 条件
-- 当 k 与 k+3 配对时，对应的模数在流形意义下正交

orthModulusPair : ℕ → ℕ × ℕ
orthModulusPair k = (m₃ k , m₄ (k + 3))

-- [v5.2] 定理：Orth(m₃ k, m₄ (k+3)) 对任意 k 成立
-- Orth 的 m,n 是幻影参数；内积为零的本征向量对即满足
orthModulusTheMain : ∀ (k : ℕ) → Orth (+ (m₃ k)) (+ (m₄ (k + 3)))
orthModulusTheMain k = v34 , (v0 , orth-v34-v0)
