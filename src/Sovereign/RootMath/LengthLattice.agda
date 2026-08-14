{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.RootMath.LengthLattice
-- 根数学：十二律长度格点序列的完整定义
-- 
-- 基准：黄钟归一化长度格点 81（无量纲整数）
-- 损益操作唯一合法的长度比例演化方式

module Sovereign.RootMath.LengthLattice where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.Product using (Σ; ∃; ∃-syntax; _,_)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Data.Fin using (Fin; zero; toℕ; fromℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Coupling.LossGain using (LossGain; Sun; Yi; applyLossGain)
open import Sovereign.Base.Lü using (LüName; HuangZhong; LinZhong; TaiCu; NanLu; GuXian; YingZhong; RuiBin; DaLu; YiZe; JiaZhong; WuShe; ZhongLu; lüToIndex; indexToLü)

--------------------------------------------------------------------------------
-- 2. 十二律长度格点序列
--------------------------------------------------------------------------------

-- 十二律长度格点（归一化整数）
lengthLattice : Vec ℕ 12
lengthLattice = 
  81 ∷  -- 黄钟（基准）
  54 ∷  -- 林钟（损一）
  72 ∷  -- 太簇（益一）
  48 ∷  -- 南吕（损一）
  64 ∷  -- 姑洗（益一）
  43 ∷  -- 应钟（损一，取整）
  57 ∷  -- 蕤宾（益一，取整）
  38 ∷  -- 大吕（损一）
  51 ∷  -- 夷则（益一，取整）
  34 ∷  -- 夹钟（损一）
  45 ∷  -- 无射（益一，取整）
  30 ∷  -- 仲吕（损一）
  []

-- 律名到长度格点
lüToLength : LüName → ℕ
lüToLength HuangZhong = 81
lüToLength LinZhong   = 54
lüToLength TaiCu      = 72
lüToLength NanLu      = 48
lüToLength GuXian     = 64
lüToLength YingZhong  = 43
lüToLength RuiBin     = 57
lüToLength DaLu       = 38
lüToLength YiZe       = 51
lüToLength JiaZhong   = 34
lüToLength WuShe      = 45
lüToLength ZhongLu    = 30

--------------------------------------------------------------------------------
-- 3. 损益链验证
--------------------------------------------------------------------------------

-- 验证每一步损益操作的正确性
data LossGainStep : Set where
  mkStep : (from to : LüName) (op : LossGain) → 
           {proof : applyLossGain (lüToLength from) op ≡ lüToLength to} → 
           LossGainStep

-- 十二律损益链
-- 2026-08 P0 轨道 A 处置: 原 twelveStepChain 为不可构造公理 —
--   LossGainStep 隐式证明要求 applyLossGain (lüToLength from) op ≡ lüToLength to,
--   但 sunOp 64 = (64·2)/3 = 42 ≠ 43 (应钟取整值), 第 5 步证明不可成立,
--   Vec LossGainStep 11 为空类型 — 假定其元素即假定 ⊥, 已删除。
--   事实: 精确 floor 损益链 (81→54→72→48→64→42→…) 与宪法取整格点
--   (…→43→57→…) 在应钟处分离; 宪法格点为权威锚定, 精确链为诊断子集。

--------------------------------------------------------------------------------
-- 4. 长度比例的代数性质
--------------------------------------------------------------------------------

-- 黄钟基准
huangzhongBase : ℕ
huangzhongBase = 81

-- 所有长度格点都是 81 通过损益操作得到
reachableFromBase : ℕ → Set
reachableFromBase n = Σ ℕ (λ steps → Σ (Vec LossGainStep steps) (λ chain → applyChain chain ≡ n))
  where
    applyChain : ∀ {n} → Vec LossGainStep n → ℕ
    applyChain [] = huangzhongBase
    applyChain (mkStep _ _ _ ∷ rest) = applyChain rest

-- 验证十二律都可达
-- 2026-08 P0 轨道 A 处置: 原 allReachable 为假命题 — 43/57/51 (取整格点)
--   不可由 sunOp/yiOp 精确链从 81 到达 (64 的下一步精确值 42 ≠ 43),
--   对应类型为空, 公理使 ⊥ 可导出, 已删除。
--   可达子集 (精确链): {81, 54, 72, 48, 64, 42, …}; 宪法取整格点为锚定,
--   不在精确链闭包内 — 两者分属"宪法长度格点"与"算术损益链"两范畴。

--------------------------------------------------------------------------------
-- 5. LCM 余数序列
--------------------------------------------------------------------------------

-- 主权 LCM 模数
SOVEREIGN_LCM : ℕ
SOVEREIGN_LCM = 11609505792

-- 3¹¹ 和 2¹⁶
POW3¹¹ : ℕ
POW3¹¹ = 177147

POW2¹⁶ : ℕ
POW2¹⁶ = 65536

-- 十二律 LCM 余数
lcmRemainders : Vec ℕ 12
lcmRemainders = 
  177147 ∷  -- 黄钟
  118098 ∷  -- 林钟
  157464 ∷  -- 太簇
  104976 ∷  -- 南吕
  139968 ∷  -- 姑洗
   93312 ∷  -- 应钟
  124416 ∷  -- 蕤宾
   82944 ∷  -- 大吕
  110592 ∷  -- 夷则
   73728 ∷  -- 夹钟
   98304 ∷  -- 无射
   65536 ∷  -- 仲吕（触发相位同步）
  []

-- 仲吕余数 = 65536 = 2¹⁶ (2026-08 P0: 原空洞 Set 公理 → refl 定理 + 构造定义)
zhongluRemainderIs65536 : lookup lcmRemainders (fromℕ 11) ≡ POW2¹⁶
zhongluRemainderIs65536 = refl

huangzhongRemainderIs177147 : lookup lcmRemainders zero ≡ POW3¹¹
huangzhongRemainderIs177147 = refl

-- 仲吕重置: LCM 环上归零 (触发相位同步 → 回到环原点)
zhonglvReset : ℕ → ℕ
zhonglvReset n = n % SOVEREIGN_LCM

-- 仲吕余数正确性: 仲吕位余数 = 2¹⁶
zhonglvCorrect : lookup lcmRemainders (fromℕ 11) ≡ POW2¹⁶
zhonglvCorrect = refl
