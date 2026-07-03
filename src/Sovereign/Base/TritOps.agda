{-# OPTIONS --guardedness #-}

-- | Sovereign.Base.TritOps
-- 基础运算：Trit 的损益操作逻辑
--
-- 核心洞察：
-- 如果 Trit 表示长度格点 L 的 3 的幂次指数 (L ≈ 3^k) 的模 3 值，
-- 那么：
-- "损一" (L × 2/3) 对应指数 -1 (模 3 循环)
-- "益一" (L × 4/3) 对应指数 +1 (模 3 循环)
--
-- 因此，损益操作在 Trit 层面上表现为**相位旋转**。

module Sovereign.Base.TritOps where

open import Sovereign.Base.Trit
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- 1. 损益操作定义 (Loss/Gain Operations)
--------------------------------------------------------------------------------

data Op : Set where
  Loss : Op  -- 损一
  Gain : Op  -- 益一

--------------------------------------------------------------------------------
-- 2. Trit 旋转逻辑 (Rotation Logic)
--------------------------------------------------------------------------------

-- 损一：相位顺时针旋转（模 3 循环：2→1→0→2）
-- 物理语义：长度格点 L × 2/3，对应指数在 {0,1,2} 中逆时针旋转
-- 严禁使用负数：这不是 -1 运算，而是模 3 循环
lossOp : Trit → Trit
lossOp T₂ = T₁  -- 表达态 → 平衡态
lossOp T₁ = T₀  -- 平衡态 → 吸收态
lossOp T₀ = T₂  -- 吸收态 → 表达态（循环）

-- 益一：相位逆时针旋转（模 3 循环：0→1→2→0）
-- 物理语义：长度格点 L × 4/3，对应指数在 {0,1,2} 中顺时针旋转
-- 严禁使用负数：这不是 +1 运算，而是模 3 循环
gainOp : Trit → Trit
gainOp T₀ = T₁  -- 吸收态 → 平衡态
gainOp T₁ = T₂  -- 平衡态 → 表达态
gainOp T₂ = T₀  -- 表达态 → 吸收态（循环）

-- 统一应用函数
applyOp : Op → Trit → Trit
applyOp Loss = lossOp
applyOp Gain = gainOp

--------------------------------------------------------------------------------
-- 3. 验证 (Verification)
--------------------------------------------------------------------------------

-- 验证：损一 3 次应回到原点 (L × 8/27 ≈ L)
lossCycle3 : ∀ (t : Trit) → lossOp (lossOp (lossOp t)) ≡ t
lossCycle3 T₂ = refl
lossCycle3 T₁ = refl
lossCycle3 T₀ = refl

-- 验证：益一 3 次应回到原点
gainCycle3 : ∀ (t : Trit) → gainOp (gainOp (gainOp t)) ≡ t
gainCycle3 T₂ = refl
gainCycle3 T₁ = refl
gainCycle3 T₀ = refl
