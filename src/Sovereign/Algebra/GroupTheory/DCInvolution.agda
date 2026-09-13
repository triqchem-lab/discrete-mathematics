{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.DCInvolution
-- DC 逆映射是对合：inv (inv x) ≡ x
--
-- 数学背景: 群 G 中 (x⁻¹)⁻¹ = x —— 逆映射是群上的对合。
-- 在类型论展示群中, 该性质按分量的联合结构分解为两条:
--   幅度分量 (GF(3) 加法): negate (negate t) ≡ t   —— 复用 Base.Trit.negate²
--   相位分量 (⟨α⟩ ≅ C₄ 乘法): alphaInv (alphaInv a) ≡ a —— 本文证明
--
-- 核心原则:
--   1. 载体 DuodecPoint = Trit × AlphaPower, 逆映射分量作用于两个分量
--   2. 分量级对合 (cong₂) 提升为联合对合, 不需要 12 case 穷举
--   3. 相位分量 alphaInv 是 ⟨α⟩ ≅ C₄ 的乘法逆, 4 case 定义性成立
--
-- 包含: alphaInv-involutive (4 case refl), duodec-inv-involutive (分量级 cong₂)
-- 0 postulate, 0 hole.

module Sovereign.Algebra.GroupTheory.DCInvolution where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Sovereign.Base.Trit using (T₀; T₁; T₂; negate²)
open import Sovereign.Algebra.GroupTheory.DuodecClock using
  (DuodecPoint; AlphaPower; a0; a1; a2; a3; alphaInv; duodec-inv)

--------------------------------------------------------------------------------
-- §1. 相位分量: alphaInv 是对合
--    alphaInv a0 = a0, a1 ↔ a3, a2 = a2, a3 ↔ a1
--    四个构造子逐一为定义性相等 (refl)
--------------------------------------------------------------------------------

alphaInv-involutive : ∀ a → alphaInv (alphaInv a) ≡ a
alphaInv-involutive a0 = refl
alphaInv-involutive a1 = refl
alphaInv-involutive a2 = refl
alphaInv-involutive a3 = refl

--------------------------------------------------------------------------------
-- §2. 联合逆映射: duodec-inv 是对合
--    duodec-inv (x , a) = (negate x , alphaInv a)
--    ⇒ duodec-inv (duodec-inv (x , a)) = (negate (negate x) , alphaInv (alphaInv a))
--    两个分量分别用 negate² 与 alphaInv-involutive, cong₂ 打包
--------------------------------------------------------------------------------

duodec-inv-involutive : ∀ p → duodec-inv (duodec-inv p) ≡ p
duodec-inv-involutive (x , a) = cong₂ _,_ (negate² x) (alphaInv-involutive a)

--------------------------------------------------------------------------------
-- §3. 对抗验证: 具体点独立 refl 交叉比对
--    定理实例必须在具体点上与直接计算一致 (原点 / 联合生成元 / 混合点)
--------------------------------------------------------------------------------

check-origin : duodec-inv (duodec-inv (T₀ , a0)) ≡ (T₀ , a0)
check-origin = refl

check-generator : duodec-inv (duodec-inv (T₁ , a1)) ≡ (T₁ , a1)
check-generator = refl

check-mixed : duodec-inv (duodec-inv (T₂ , a3)) ≡ (T₂ , a3)
check-mixed = refl
