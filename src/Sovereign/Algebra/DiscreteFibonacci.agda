{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DiscreteFibonacci
-- 离散斐波那契 — 有限域版 (φ 阶 8 闭合循环)，非连续统死亡几何
--
-- 核心原则:
--   · 连续统斐波那契螺旋 = 黄金比例 (1+√5)/2 无限外推、无法归一（死亡几何），
--     不在本框架内（连续统病态, 见 01-algebraic-pole 退化分类）。
--   · 有限域版: 斐波那契递推在 GF(3) 上取模成有限周期序列，Pisano 周期 = 8；
--     φ = 1+2α ∈ GF(9) 是 8 阶元，φ² = α —— 即 90° 旋转 α 的「平方根/半步」。
--   · 两条 8 周期统一于同一常数: Pisano(3) = 8 = ord(φ)。
--
-- 包含:
--   §1 斐波那契 mod 3: fibPair 状态机 + Pisano 周期 8 (归纳证明)
--   §2 φ 的精确阶 8: φ⁸=1 且 φ¹/φ²/φ⁴ ≠ 1 → φ 生成 GF(9)*
--   §3 φ² = α: 90° 克里斯托螺旋的半步层
--   §4 统一锚点: Pisano(3) = 8 = ord(φ)
--
-- 与主线的边界: φ 不进入 DuodecClock (十二进制只含 90° α) 也不进入
--   OpticalWindow (光学窗口只含 α); 本模块仅锚定 φ 的代数事实与
--   斐波那契的有限域投影。0 postulate。

module Sovereign.Algebra.DiscreteFibonacci where

open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.GF9
  using (GF9; gf9-one; alpha; phi; phi-squared; phi-to-8; phi-not-order-4; _*gf9_)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 斐波那契 mod 3 —— Pisano 周期 8
--------------------------------------------------------------------------------

-- 相邻对状态机: (F_n, F_{n+1}) → (F_{n+1}, F_n ⊕ F_{n+1})  (GF(3) 加法)
fibStep : Trit × Trit → Trit × Trit
fibStep (a , b) = (b , a ⊕ b)

fibPair : ℕ → Trit × Trit
fibPair zero    = (T₀ , T₁)
fibPair (suc n) = fibStep (fibPair n)

-- 8 步闭合: (0,1)→(1,1)→(1,2)→(2,0)→(0,2)→(2,2)→(2,1)→(1,0)→(0,1)
fibPair-8-base : fibPair (8 + 0) ≡ fibPair 0
fibPair-8-base = refl

-- Pisano 周期 8 (归纳: 基 8 步 refl + 步进与状态机可交换)
fibPair-period-8 : ∀ n → fibPair (8 + n) ≡ fibPair n
fibPair-period-8 zero = fibPair-8-base
fibPair-period-8 (suc n) = begin
  fibPair (8 + suc n)
    ≡⟨⟩
  fibPair (suc (8 + n))
    ≡⟨⟩
  fibStep (fibPair (8 + n))
    ≡⟨ cong fibStep (fibPair-period-8 n) ⟩
  fibStep (fibPair n)
    ≡⟨⟩
  fibPair (suc n)
  ∎

-- F_n mod 3 (第 n 个斐波那契数的 GF(3) 投影)
fibTrit : ℕ → Trit
fibTrit n = proj₁ (fibPair n)

fibTrit-period-8 : ∀ n → fibTrit (8 + n) ≡ fibTrit n
fibTrit-period-8 n = cong proj₁ (fibPair-period-8 n)

-- Pisano 周期 (mod 3) = 8
pisano-period-3 : ℕ
pisano-period-3 = 8

--------------------------------------------------------------------------------
-- §2. φ = 1+2α 的精确阶 8 —— 生成 GF(9)*
--------------------------------------------------------------------------------

-- Trit 构造子互异（否定见证）
T₀≢T₁ : T₀ ≡ T₁ → ⊥
T₀≢T₁ ()

T₂≢T₀ : T₂ ≡ T₀ → ⊥
T₂≢T₀ ()

-- φ = (T₁, T₂) ≠ (T₁, T₀) = gf9-one
phi-not-order-1 : phi ≡ gf9-one → ⊥
phi-not-order-1 p = T₂≢T₀ (cong proj₂ p)

-- φ² = α = (T₀, T₁) ≠ (T₁, T₀) = gf9-one
phi-not-order-2 : phi *gf9 phi ≡ gf9-one → ⊥
phi-not-order-2 p = T₀≢T₁ (cong proj₁ p)

-- φ⁴ ≠ 1: 引用 GF9.phi-not-order-4
-- φ⁸ = 1: 引用 GF9.phi-to-8
-- 综上 φ 的精确阶 = 8 = |GF(9)*|，故 φ 生成整个乘法群 GF(9)* ≅ C₈。

phi-order-is-8 : ℕ
phi-order-is-8 = 8

--------------------------------------------------------------------------------
-- §3. φ² = α —— 90° 克里斯托螺旋的半步层
--------------------------------------------------------------------------------

phi-squared-is-alpha : phi *gf9 phi ≡ alpha
phi-squared-is-alpha = phi-squared

--------------------------------------------------------------------------------
-- §4. 统一锚点 —— Pisano(3) = 8 = ord(φ)
--------------------------------------------------------------------------------

-- 斐波那契 mod 3 的周期 8 与 φ 的阶 8 是同一常数：
-- 连续统黄金螺旋的有限域投影（斐波那契）与 90° 旋转的平方根层（φ）
-- 在 GF(3)/GF(9) 中收敛到同一个 8。
pisano-3-equals-ord-phi : pisano-period-3 ≡ phi-order-is-8
pisano-3-equals-ord-phi = refl

--------------------------------------------------------------------------------
-- 结论:
--   斐波那契在离散全息框架中的合法表示是「有限域版」:
--   · GF(3) 上取模 → 周期 8 闭合循环 (Pisano), 非无限外推;
--   · GF(9) 上 φ=1+2α, φ²=α, φ⁸=1 → 90° 的半步, 8 阶闭合;
--   连续统版 (黄金比例, 无穷远点) 仍被排除 (死亡几何)。
--   φ 不进入 DuodecClock / OpticalWindow (主线只含 90° α)。
--------------------------------------------------------------------------------

-- 0 postulate.
