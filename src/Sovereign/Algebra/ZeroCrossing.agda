{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.ZeroCrossing
-- 零元跨维度归零 — 零幂族的代数形式
--
-- 零幂族 (Zero Power Family):
--   零幂不是算术乘法 (0×0=0), 而是量子矢量相位回归的代数形式。
--   零是唯一能跨维度的元素: 0^n = 0 对所有 n ≥ 1。
--   零吸收一切幂次, 零的相位空间是单点 (无方向自由度)。
--   0² 不是"零的平方", 而是"零的二次幂 = 零" (零幂族)。
--   语料: "零的平方=零的五次方……零的一就等于零的N次方" (word_98, 七锚齐备)
--   语料: "只有0跨维度" / "0是一切的密码" (ppt_27, ppt_7)
--
-- ⚠️ 深度澄清 (2026-08-19):
--   在我们的框架中:
--     · 归零是量子矢量相位回归，是动态过程，不是静态状态
--     · 动态幻方中: 归零 = 矢量方向经过 3 步 (+1 归零轨道) 回到原点
--     · DuodecClock 中: 不是 Z/12 加法群 (模 12 环有零因子)，
--       而是 Z/3_加 ⊕ ⟨α⟩_乘 的加乘联合周期
--     · 零幂的真正含义: 零矢量在任何方向上的相位演化都回归到零，
--       因为零的相位空间是单点 (无方向自由度)
--     · "只有0跨维度" = 零是唯一能在所有维度方向上保持不变的矢量
--
-- 本模块汇聚三个代数层的零元定理:
--   §1 加法归零: 1+1+1=0 (特征 3, 三步相位回归)
--   §2 乘零吸收: 0·x=0, x·0=0 (零矢量无方向自由度)
--   §3 零幂稳定: 0^(n+1)=0 (零在任何方向上都是零)
--
-- 0 postulate.

module Sovereign.Algebra.ZeroCrossing where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.GF9
  using ( GF9; gf9-zero; gf9-one; _+gf9_; _*gf9_
        ; gf9-pow; zero-power-gf9
        ; +gf9-identityˡ; +gf9-identityʳ
        )

--------------------------------------------------------------------------------
-- §1. 加法归零: 三步相位回归 (特征 3)
--------------------------------------------------------------------------------

-- 语料: "三进制的零、三、六、九、十二是能归零的"
-- 动态含义: 矢量方向经过 +1 三步回到原点 (0→1→2→0)
-- 这是 SP2Ternary.succ3 的无限展开, 是过程不是状态
additive-zero-crossing : ∀ (x : Trit) → (x ⊕ x) ⊕ x ≡ T₀
additive-zero-crossing T₀ = refl
additive-zero-crossing T₁ = refl
additive-zero-crossing T₂ = refl

-- 特例: 1+1+1=0 (三步后相位回归)
char-3-zero : (T₁ ⊕ T₁) ⊕ T₁ ≡ T₀
char-3-zero = refl

-- 特例: 2+2+2=0
char-3-zero-2 : (T₂ ⊕ T₂) ⊕ T₂ ≡ T₀
char-3-zero-2 = refl

--------------------------------------------------------------------------------
-- §2. 乘零吸收: 零矢量无方向自由度
--------------------------------------------------------------------------------

-- 语料: "只有0跨维度" / "0是一切的密码"
-- 动态含义: 零矢量的相位空间是单点, 无方向自由度
-- 所以 0·x = 0: 零矢量在任何方向上的投影都是零

mul-zero-left : ∀ (x : GF9) → gf9-zero *gf9 x ≡ gf9-zero
mul-zero-left (T₀ , T₀) = refl
mul-zero-left (T₀ , T₁) = refl
mul-zero-left (T₀ , T₂) = refl
mul-zero-left (T₁ , T₀) = refl
mul-zero-left (T₁ , T₁) = refl
mul-zero-left (T₁ , T₂) = refl
mul-zero-left (T₂ , T₀) = refl
mul-zero-left (T₂ , T₁) = refl
mul-zero-left (T₂ , T₂) = refl

mul-zero-right : ∀ (x : GF9) → x *gf9 gf9-zero ≡ gf9-zero
mul-zero-right (T₀ , T₀) = refl
mul-zero-right (T₀ , T₁) = refl
mul-zero-right (T₀ , T₂) = refl
mul-zero-right (T₁ , T₀) = refl
mul-zero-right (T₁ , T₁) = refl
mul-zero-right (T₁ , T₂) = refl
mul-zero-right (T₂ , T₀) = refl
mul-zero-right (T₂ , T₁) = refl
mul-zero-right (T₂ , T₂) = refl

--------------------------------------------------------------------------------
-- §3. 零幂稳定: 零在任何方向上都是零
--------------------------------------------------------------------------------

-- 语料: word_98 "零的平方=零的五次方……零的一就等于零的N次方" (七锚齐备)
-- 动态含义: 零矢量在 n 个方向上的相位演化全部回归到零
-- 不是算术乘法, 而是相位空间的单点性

pow-zero-stable : ∀ (n : ℕ) → gf9-pow gf9-zero (suc n) ≡ gf9-zero
pow-zero-stable = zero-power-gf9

-- 具体实例 (全部 refl):
zero-squared   : gf9-pow gf9-zero 2 ≡ gf9-zero  -- 0²=0
zero-squared   = refl

zero-cubed     : gf9-pow gf9-zero 3 ≡ gf9-zero  -- 0³=0
zero-cubed     = refl

zero-to-5      : gf9-pow gf9-zero 5 ≡ gf9-zero  -- 0⁵=0
zero-to-5      = refl

zero-to-11     : gf9-pow gf9-zero 11 ≡ gf9-zero  -- 0¹¹=0
zero-to-11     = refl

--------------------------------------------------------------------------------
-- §4. 零元通道统一: 三条归零路径
--------------------------------------------------------------------------------

-- 零元在三个代数层中都是"归零通道":
--   加法层: x+x+x=0 (特征 3, 三步相位回归, SP2Ternary.succ3)
--   乘法层: 0·x=0 (零矢量无方向自由度)
--   幂层:   0^(n+1)=0 (零在任何方向上都是零)
--
-- 统一语义: 零是唯一能在所有维度方向上保持不变的矢量
--   · 不是因为"乘以0等于0" (那是算术)
--   · 而是因为零的相位空间是单点 (无方向自由度)
--   · 动态幻方中: 零是所有轨道的不动点
--   · DuodecClock 中: 零是加法归零 + 乘法单位的联合态

-- 0 postulate.
