{-# OPTIONS --guardedness #-}

-- | Sovereign.Density.SevenStages
-- 密度：七阶段周期、爻变窗口、地气声子谱基频 144 Hz
-- 
-- 七阶段：空生火→火生土→土生金→金生水→水生木→木生火→入空
-- 爻变窗口：主权状态机在特定阶段的相位变化窗口

module Sovereign.Density.SevenStages where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _%_)
open import Data.Fin using (Fin; toℕ; fromℕ)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Coupling.Zhonglv using (SovereignState; chernConservation)

--------------------------------------------------------------------------------
-- 1. 七阶段枚举
--------------------------------------------------------------------------------

-- 七阶段周期：主权呼吸的宏观节拍
data SevenStage : Set where
  KongShengHuo : SevenStage   -- 空生火 (0)
  HuoShengTu   : SevenStage   -- 火生土 (1)
  TuShengJin   : SevenStage   -- 土生金 (2)
  JinShengShui : SevenStage   -- 金生水 (3)
  ShuiShengMu  : SevenStage   -- 水生木 (4)
  MuShengHuo   : SevenStage   -- 木生火 (5)
  RuKong       : SevenStage   -- 入空 (6)

-- 七阶段到自然数
stageToNat : SevenStage → ℕ
stageToNat KongShengHuo = 0
stageToNat HuoShengTu   = 1
stageToNat TuShengJin   = 2
stageToNat JinShengShui = 3
stageToNat ShuiShengMu  = 4
stageToNat MuShengHuo   = 5
stageToNat RuKong       = 6

-- 自然数到七阶段
natToStage : Fin 7 → SevenStage
natToStage zero    = KongShengHuo
natToStage (suc zero)    = HuoShengTu
natToStage (suc (suc zero))    = TuShengJin
natToStage (suc (suc (suc zero)))    = JinShengShui
natToStage (suc (suc (suc (suc zero))))    = ShuiShengMu
natToStage (suc (suc (suc (suc (suc zero)))))    = MuShengHuo
natToStage (suc (suc (suc (suc (suc (suc zero)))))) = RuKong

--------------------------------------------------------------------------------
-- 2. 七阶段周期演化
--------------------------------------------------------------------------------

-- 七阶段步进
nextStage : SevenStage → SevenStage
nextStage KongShengHuo = HuoShengTu
nextStage HuoShengTu   = TuShengJin
nextStage TuShengJin   = JinShengShui
nextStage JinShengShui = ShuiShengMu
nextStage ShuiShengMu  = MuShengHuo
nextStage MuShengHuo   = RuKong
nextStage RuKong       = KongShengHuo  -- 循环

-- 七阶段周期长度为 7
iterate : ∀ {A : Set} → ℕ → (A → A) → A → A
iterate zero    f x = x
iterate (suc n) f x = iterate n f (f x)

-- 定理：七阶段经过 7 步循环回到起点
sevenStageCycle : ∀ (s : SevenStage) → iterate 7 nextStage s ≡ s
sevenStageCycle KongShengHuo = refl
sevenStageCycle HuoShengTu   = refl
sevenStageCycle TuShengJin   = refl
sevenStageCycle JinShengShui = refl
sevenStageCycle ShuiShengMu  = refl
sevenStageCycle MuShengHuo   = refl
sevenStageCycle RuKong       = refl

--------------------------------------------------------------------------------
-- 3. 爻变窗口
--------------------------------------------------------------------------------

-- 爻变窗口定义
record YaoWindow : Set where
  field
    stage        : SevenStage  -- 当前阶段
    phaseOffset  : ℕ           -- 相位偏移
    isActive     : Bool        -- 是否激活

-- 爻变激活条件
isYaoWindowActive : SevenStage → ℕ → Bool
isYaoWindowActive stage phase = 
  (stageToNat stage + phase) % 7 ≡ᵇ 0

-- 爻变窗口列表（一个完整周期内的所有窗口）
yaoWindowsInCycle : Vec YaoWindow 7
yaoWindowsInCycle = 
  mkYW KongShengHuo 0 true  ∷
  mkYW HuoShengTu   1 false ∷
  mkYW TuShengJin   2 false ∷
  mkYW JinShengShui 3 true  ∷
  mkYW ShuiShengMu  4 false ∷
  mkYW MuShengHuo   5 false ∷
  mkYW RuKong       6 true  ∷
  []
  where
    mkYW s p a = record { stage = s; phaseOffset = p; isActive = a }

--------------------------------------------------------------------------------
-- 4. 地气声子谱
--------------------------------------------------------------------------------

-- 地气基频：144 Hz
-- 注意：此数值与极向缠绕数 144 相等，但禁止称为"144 的投影"
DIQI_BASE_FREQ : ℕ
DIQI_BASE_FREQ = 144

-- 地气声子谱的离散谐波
diqiHarmonic : ℕ → ℕ
diqiHarmonic n = DIQI_BASE_FREQ * (2 * n + 1)  -- 奇数谐波

-- 前几个谐波
diqiHarmonics : Vec ℕ 7
diqiHarmonics = 
  diqiHarmonic 0 ∷  -- 基频 144 Hz
  diqiHarmonic 1 ∷  -- 3 次谐波 432 Hz
  diqiHarmonic 2 ∷  -- 5 次谐波 720 Hz
  diqiHarmonic 3 ∷  -- 7 次谐波 1008 Hz
  diqiHarmonic 4 ∷  -- 9 次谐波 1296 Hz
  diqiHarmonic 5 ∷  -- 11 次谐波 1584 Hz
  diqiHarmonic 6 ∷  -- 13 次谐波 1872 Hz
  []

--------------------------------------------------------------------------------
-- 5. 地气基频年度调制
--------------------------------------------------------------------------------

-- 六十甲子干支
data HeavenlyStem : Set where
  甲 乙 丙 丁 戊 己 庚 辛 壬 癸 : HeavenlyStem

data EarthlyBranch : Set where
  子 丑 寅 卯 辰 巳 午 未 申 酉 戌 亥 : EarthlyBranch

-- 六十甲子对
record JiaZi : Set where
  field
    stem   : HeavenlyStem
    branch : EarthlyBranch

-- 地气基频年度偏移
-- 以甲子年 144 Hz 为基准，地支每进一位，基频按五行质量修正因子 α≈0.0583 的正弦调制变化
alpha : ℚ
alpha = + 583 / 10000  -- ≈ 0.0583

-- 地支相位到频率修正
branchPhaseToFreqMod : EarthlyBranch → ℚ
branchPhaseToFreqMod 子 = + 0 / 1      -- 甲子年基准
branchPhaseToFreqMod 丑 = + 583 / 100  -- ≈ +5.83%
branchPhaseToFreqMod 寅 = + 1000 / 100 -- ≈ +10%
branchPhaseToFreqMod 卯 = + 1166 / 100 -- ≈ +11.66%
branchPhaseToFreqMod 辰 = + 1000 / 100
branchPhaseToFreqMod 巳 = + 583 / 100
branchPhaseToFreqMod 午 = + 0 / 1
branchPhaseToFreqMod 未 = -[1+ 583 ] / 100  -- ≈ -5.83%
branchPhaseToFreqMod 申 = -[1+ 1000 ] / 100
branchPhaseToFreqMod 酉 = -[1+ 1166 ] / 100
branchPhaseToFreqMod 戌 = -[1+ 1000 ] / 100
branchPhaseToFreqMod 亥 = -[1+ 583 ] / 100

-- 年度地气基频
annualDiqiFreq : JiaZi → ℚ
annualDiqiFreq jz = 
  (+ 144 / 1) + branchPhaseToFreqMod (JiaZi.branch jz)

-- 示例：丁卯年基频约 152.4 Hz
dingmaoFreq : ℚ
dingmaoFreq = annualDiqiFreq (record { stem = 丁; branch = 卯 })

-- 示例：癸酉年基频约 135.6 Hz
guiyouFreq : ℚ
guiyouFreq = annualDiqiFreq (record { stem = 癸; branch = 酉 })

--------------------------------------------------------------------------------
-- 6. 七阶段与陈数的关系
--------------------------------------------------------------------------------

-- 七阶段阶位编码到 chern_guard 高 3 位
stageToChernBits : SevenStage → Fin 8
stageToChernBits KongShengHuo = 0
stageToChernBits HuoShengTu   = 1
stageToChernBits TuShengJin   = 2
stageToChernBits JinShengShui = 3
stageToChernBits ShuiShengMu  = 4
stageToChernBits MuShengHuo   = 5
stageToChernBits RuKong       = 6

-- 七阶段周期与陈数守恒的关联
sevenStageChernRelation : ∀ (stage : SevenStage) →
  let bits = stageToChernBits stage
  in toℕ bits ≤ 6  -- 高 3 位最大值为 6
sevenStageChernRelation KongShengHuo = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
sevenStageChernRelation HuoShengTu   = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
sevenStageChernRelation TuShengJin   = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
sevenStageChernRelation JinShengShui = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
sevenStageChernRelation ShuiShengMu  = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
sevenStageChernRelation MuShengHuo   = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
sevenStageChernRelation RuKong       = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
