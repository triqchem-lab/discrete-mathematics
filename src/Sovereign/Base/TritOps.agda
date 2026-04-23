{-# OPTIONS --cubical --guardedness #-}

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

--------------------------------------------------------------------------------
-- 1. 损益操作定义 (Loss/Gain Operations)
--------------------------------------------------------------------------------

data Op : Set where
  Loss : Op  -- 损一
  Gain : Op  -- 益一

--------------------------------------------------------------------------------
-- 2. Trit 旋转逻辑 (Rotation Logic)
--------------------------------------------------------------------------------

-- 损一：指数 -1 (顺时针旋转)
-- T+ (1) -> T0 (0) -> T- (-1) -> T+ (1)
lossOp : Trit → Trit
lossOp T+ = T0
lossOp T0 = T-
lossOp T- = T+ -- 循环

-- 益一：指数 +1 (逆时针旋转)
-- T- (-1) -> T0 (0) -> T+ (1) -> T- (-1)
gainOp : Trit → Trit
gainOp T- = T0
gainOp T0 = T+
gainOp T+ = T- -- 循环

-- 统一应用函数
applyOp : Op → Trit → Trit
applyOp Loss = lossOp
applyOp Gain = gainOp

--------------------------------------------------------------------------------
-- 3. 验证 (Verification)
--------------------------------------------------------------------------------

-- 验证：损一 3 次应回到原点 (L × 8/27 ≈ L)
lossCycle3 : ∀ (t : Trit) → lossOp (lossOp (lossOp t)) ≡ t
lossCycle3 T+ = refl
lossCycle3 T0 = refl
lossCycle3 T- = refl

-- 验证：益一 3 次应回到原点
gainCycle3 : ∀ (t : Trit) → gainOp (gainOp (gainOp t)) ≡ t
gainCycle3 T+ = refl
gainCycle3 T0 = refl
gainCycle3 T- = refl
