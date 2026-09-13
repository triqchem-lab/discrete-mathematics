{-# OPTIONS --guardedness #-}

-- | Sovereign.MetaStructure.WuXing
-- 元结构层：五行模数区定义与动力学关系
--
-- 核心概念：
-- 五行（火土木水金）不是物质元素，而是主权状态机在环向缠绕中的
-- **共振模数区** (Resonance Modulus Zones)。
-- 它们定义了系统演化的拓扑约束和手性倾向。

module Sovereign.MetaStructure.WuXing where

open import Data.Nat using (ℕ; _+_; _*_; _mod_)
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (Vec)

--------------------------------------------------------------------------------
-- 1. 五行元素定义 (Elements)
--------------------------------------------------------------------------------

data WuXing : Set where
  Fire  : WuXing  -- 火 (模数 2)
  Earth : WuXing  -- 土 (模数 5)
  Metal : WuXing  -- 金 (模数 4)
  Water : WuXing  -- 水 (模数 6)
  Wood  : WuXing  -- 木 (模数 8)

-- 五行基数映射 (宪法定义)
wuXingBase : WuXing → ℕ
wuXingBase Fire  = 2
wuXingBase Earth = 5
wuXingBase Metal = 4
wuXingBase Water = 6
wuXingBase Wood  = 8

-- 映射到索引 0-4 (用于数组/向量访问)
wuXingToIndex : WuXing → Fin 5
wuXingToIndex Fire  = 0
wuXingToIndex Earth = 1
wuXingToIndex Metal = 2
wuXingToIndex Water = 3
wuXingToIndex Wood  = 4

--------------------------------------------------------------------------------
-- 2. 五行关系动力学 (Dynamics)
--------------------------------------------------------------------------------

-- 相生关系 (Generating Cycle): 火→土→金→水→木→火
-- 这是主权状态机在正常演化中的路径
generate : WuXing → WuXing
generate Fire  = Earth
generate Earth = Metal
generate Metal = Water
generate Water = Wood
generate Wood  = Fire

-- 相克关系 (Overcoming Cycle): 火→金→木→土→水→火
-- 这是导致手性分离和能隙打开的干涉路径
overcome : WuXing → WuXing
overcome Fire  = Metal
overcome Metal = Wood
overcome Wood  = Earth
overcome Earth = Water
overcome Water = Fire

--------------------------------------------------------------------------------
-- 3. 状态机集成辅助 (Integration Helpers)
--------------------------------------------------------------------------------

-- 当前五行模数区 (根据步骤数计算)
-- 假设 12 律对应五行的循环分布
getCurrentWuXing : Fin 12 → WuXing
getCurrentWuXing step with toℕ step
... | 0 = Fire  -- 黄钟
... | 1 = Fire  -- 林钟
... | 2 = Earth -- 太簇
... | 3 = Earth -- 南吕
... | 4 = Metal -- 姑洗
... | 5 = Metal -- 应钟
... | 6 = Water -- 蕤宾
... | 7 = Water -- 大吕
... | 8 = Wood  -- 夷则
... | 9 = Wood  -- 夹钟
... | 10 = Fire -- 无射 (循环回火，或根据具体定义调整)
... | 11 = Fire -- 仲吕

-- 验证：五行基数是否匹配宪法
postulate
  wuXingBasesCorrect : 
    wuXingBase Fire  ≡ 2 ×
    wuXingBase Earth ≡ 5 ×
    wuXingBase Metal ≡ 4 ×
    wuXingBase Water ≡ 6 ×
    wuXingBase Wood  ≡ 8 ≡ True
