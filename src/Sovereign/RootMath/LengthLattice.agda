{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.RootMath.LengthLattice
-- 根数学：十二律长度格点序列的完整定义
-- 
-- 基准：黄钟归一化长度格点 81（无量纲整数）
-- 损益操作唯一合法的长度比例演化方式

module Sovereign.RootMath.LengthLattice where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Data.Fin using (Fin; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Coupling.LossGain using (LossGain; Sun; Yi; applyLossGain)

--------------------------------------------------------------------------------
-- 1. 十二律枚举
--------------------------------------------------------------------------------

data LüName : Set where
  HuangZhong LinZhong TaiCu NanLu GuXian YingZhong 
  RuiBin DaLu YiZe JiaZhong WuShe ZhongLu : LüName

-- 律名到索引
lüToIndex : LüName → Fin 12
lüToIndex HuangZhong = 0
lüToIndex LinZhong   = 1
lüToIndex TaiCu      = 2
lüToIndex NanLu      = 3
lüToIndex GuXian     = 4
lüToIndex YingZhong  = 5
lüToIndex RuiBin     = 6
lüToIndex DaLu       = 7
lüToIndex YiZe       = 8
lüToIndex JiaZhong   = 9
lüToIndex WuShe      = 10
lüToIndex ZhongLu    = 11

-- 索引到律名
indexToLü : Fin 12 → LüName
indexToLü 0  = HuangZhong
indexToLü 1  = LinZhong
indexToLü 2  = TaiCu
indexToLü 3  = NanLu
indexToLü 4  = GuXian
indexToLü 5  = YingZhong
indexToLü 6  = RuiBin
indexToLü 7  = DaLu
indexToLü 8  = YiZe
indexToLü 9  = JiaZhong
indexToLü 10 = WuShe
indexToLü 11 = ZhongLu

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
twelveStepChain : Vec LossGainStep 11
twelveStepChain = 
  mkStep HuangZhong LinZhong Sun ∷   -- 81 * 2/3 = 54 ✓
  mkStep LinZhong   TaiCu    Yi  ∷   -- 54 * 4/3 = 72 ✓
  mkStep TaiCu      NanLu    Sun ∷   -- 72 * 2/3 = 48 ✓
  mkStep NanLu      GuXian   Yi  ∷   -- 48 * 4/3 = 64 ✓
  mkStep GuXian     YingZhong Sun ∷  -- 64 * 2/3 ≈ 42.67 → 43
  mkStep YingZhong  RuiBin   Yi  ∷   -- 43 * 4/3 ≈ 57.33 → 57
  mkStep RuiBin     DaLu     Sun ∷   -- 57 * 2/3 = 38 ✓
  mkStep DaLu       YiZe     Yi  ∷   -- 38 * 4/3 ≈ 50.67 → 51
  mkStep YiZe       JiaZhong Sun ∷   -- 51 * 2/3 = 34 ✓
  mkStep JiaZhong   WuShe    Yi  ∷   -- 34 * 4/3 ≈ 45.33 → 45
  mkStep WuShe      ZhongLu  Sun ∷   -- 45 * 2/3 = 30 ✓
  []

--------------------------------------------------------------------------------
-- 4. 长度比例的代数性质
--------------------------------------------------------------------------------

-- 黄钟基准
huangzhongBase : ℕ
huangzhongBase = 81

-- 所有长度格点都是 81 通过损益操作得到
reachableFromBase : ℕ → Set
reachableFromBase n = ∃[ steps ] ∃[ chain : Vec LossGainStep steps ] 
                      applyChain 11 chain ≡ n
  where
    applyChain : ℕ → Vec LossGainStep ℕ → ℕ
    applyChain zero _ = huangzhongBase
    applyChain (suc _) (mkStep _ _ _ ∷ rest) = applyChain _ rest

-- 验证十二律都可达
allReachable : ∀ (lü : LüName) → reachableFromBase (lüToLength lü)
allReachable HuangZhong = ?  -- 0 steps
allReachable LinZhong   = ?  -- 1 step: Sun
allReachable TaiCu      = ?  -- 2 steps: Sun, Yi
allReachable _ = ?  -- 等等

--------------------------------------------------------------------------------
-- 5. LCM 余数序列
--------------------------------------------------------------------------------

-- 主权 LCM 模数
SOVEREIGN_LCM : ℕ
SOVEREIGN_LCM = 11609505792

-- 3¹¹ 和 2¹⁶
POWER3_11 : ℕ
POWER3_11 = 177147

POWER2_16 : ℕ
POWER2_16 = 65536

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
   65536 ∷  -- 仲吕（触发闭合）
  []

-- 仲吕余数 = 65536 = 2¹⁶
zhongluRemainderIs65536 : lookup 11 lcmRemainders ≡ POWER2_16
zhongluRemainderIs65536 = refl

-- 黄钟余数 = 177147 = 3¹¹
huangzhongRemainderIs177147 : lookup 0 lcmRemainders ≡ POWER3_11
huangzhongRemainderIs177147 = refl

--------------------------------------------------------------------------------
-- 6. 仲吕闭合复位
--------------------------------------------------------------------------------

-- 仲吕闭合将余数从 65536 复位到 177147
zhonglvReset : ℕ → ℕ
zhonglvReset 65536 = 177147  -- 仲吕 → 黄钟
zhonglvReset _     = ?       -- 其他情况

-- 闭合验证
zhonglvCorrect : zhonglvReset (lookup 11 lcmRemainders) ≡ lookup 0 lcmRemainders
zhonglvCorrect = refl
