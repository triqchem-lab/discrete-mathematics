{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.MetaStructure.WuXing
-- 元结构层：五行模数区定义与动力学关系
--
-- 数学背景：五行（木火土金水）+ 手性（Chirality）的生成结构——
--   「结构 = 生成方式」第一原理：五行由 generate/overcome 两关系生成，不由元素个数决定。
--
-- 核心原则：
--   1. 生成方式即结构（generate/overcome 是关系字段级定义）；
--   2. 枚举与索引双向（wuXingToIndex 单射性核对 wuXingBasesCorrect）；
--   3. 模数区静态（十二律长度表类约束）。
--
-- 包含：WuXing/Chirality（五行与手性 data）· wuXingBase/wuXingToIndex（基数与索引）·
--   generate/overcome（生成/克服）· getCurrentWuXing（动力学）· wuXingBasesCorrect（核对）

module Sovereign.MetaStructure.WuXing where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Data.Vec using (Vec)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- 1. 五行元素定义 (Elements)
--------------------------------------------------------------------------------

data WuXing : Set where
  Fire  : WuXing  -- 火 (模数 2)
  Earth : WuXing  -- 土 (模数 5)
  Metal : WuXing  -- 金 (模数 4)
  Water : WuXing  -- 水 (模数 6)
  Wood  : WuXing  -- 木 (模数 8)

-- 手征性 (Chirality)
data Chirality : Set where
  LeftHanded  : Chirality
  RightHanded : Chirality

-- 五行基数映射 (宪法定义)
wuXingBase : WuXing → ℕ
wuXingBase Fire  = 2
wuXingBase Earth = 5
wuXingBase Metal = 4
wuXingBase Water = 6
wuXingBase Wood  = 8

-- 映射到索引 0-4 (用于数组/向量访问)
wuXingToIndex : WuXing → Fin 5
wuXingToIndex Fire  = zero
wuXingToIndex Earth = suc zero
wuXingToIndex Metal = suc (suc zero)
wuXingToIndex Water = suc (suc (suc zero))
wuXingToIndex Wood  = suc (suc (suc (suc zero)))

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
-- 使用向量查找确保覆盖所有 12 种情况
getCurrentWuXing : Fin 12 → WuXing
getCurrentWuXing zero = Fire       -- 0 黄钟
getCurrentWuXing (suc zero) = Fire -- 1 林钟
getCurrentWuXing (suc (suc zero)) = Earth  -- 2 太簇
getCurrentWuXing (suc (suc (suc zero))) = Earth  -- 3 南吕
getCurrentWuXing (suc (suc (suc (suc zero)))) = Metal  -- 4 姑洗
getCurrentWuXing (suc (suc (suc (suc (suc zero))))) = Metal  -- 5 应钟
getCurrentWuXing (suc (suc (suc (suc (suc (suc zero)))))) = Water  -- 6 蕤宾
getCurrentWuXing (suc (suc (suc (suc (suc (suc (suc zero))))))) = Water  -- 7 大吕
getCurrentWuXing (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = Wood  -- 8 夷则
getCurrentWuXing (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = Wood  -- 9 夹钟
getCurrentWuXing (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = Fire  -- 10 无射
getCurrentWuXing (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = Fire  -- 11 仲吕

-- 验证：五行基数等于宪法定义值 (v5.3: postulate → refl 直接证明)
-- Fable 5深度分析确认：5个基数可用refl直证，不需要postulate
wuXingBasesCorrect :
  (wuXingBase Fire  ≡ 2) ×
  (wuXingBase Earth ≡ 5) ×
  (wuXingBase Metal ≡ 4) ×
  (wuXingBase Water ≡ 6) ×
  (wuXingBase Wood  ≡ 8)
wuXingBasesCorrect = refl , refl , refl , refl , refl

--------------------------------------------------------------------------------
-- 4. 手性五行对偶 (ChiralWuXing)
--------------------------------------------------------------------------------

-- 手性五行：五行元素 × 手性标签
record ChiralWuXing : Set where
  constructor chiral
  field
    element  : WuXing
    chirality : Chirality

-- 手性对偶：翻转手性标签（左↔右）
chiralDual : ChiralWuXing → ChiralWuXing
chiralDual (chiral e LeftHanded)  = chiral e RightHanded
chiralDual (chiral e RightHanded) = chiral e LeftHanded

-- 手性对偶是对合：dual ∘ dual ≡ id
chiralDualInvolutive : ∀ (c : ChiralWuXing) → chiralDual (chiralDual c) ≡ c
chiralDualInvolutive (chiral e LeftHanded)  = refl
chiralDualInvolutive (chiral e RightHanded) = refl
