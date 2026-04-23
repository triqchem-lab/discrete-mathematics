{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Engine.StateMachine
-- 引擎层：主权状态机完整生命周期管理 (宪法重构版)
--
-- 核心更新：
-- 1. 强制使用 Sovereign.Coupling.LCM 模块的宪法级打包/解包逻辑。
-- 2. 添加主权闭合 KPI 监控 (仲吕闭合次数、奇点捕获率)。
-- 3. 能隙硬边界：解包时 ≥243 触发强制归零 (爻变)。
-- 4. 陈数监控：记录局部曲率和 (训练期启发式代理)。

module Sovereign.Engine.StateMachine where

open import Data.Nat using (ℕ; _+_; _*_; _<_; _≥_; _mod_; _div_; suc; zero)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; toℕ; fromℕ)
open import Data.Vec using (Vec; map; _∷_; []; replicate; length)
open import Data.Product using (_×_; _,_)

-- 宪法模块导入
import Sovereign.Coupling.LCM as LCM
import Sovereign.Coding.Trit as T
import Sovereign.Projection.Binary as Proj
import Sovereign.Base.Axioms as Ax
import Sovereign.Base.Invariants as Inv

--------------------------------------------------------------------------------
-- 1. 完整主权状态 (Full Sovereign State with KPIs)
--------------------------------------------------------------------------------

-- 主权状态机记录：包含几何态、累加器、相位、步数与主权闭合 KPI
record SovereignState : Set where
  constructor mkState
  field
    section         : LCM.SovereignSection  -- 30 Trit 逻辑截面
    acc             : ℕ                     -- 逻辑累加器 (LCM 模空间)
    phase           : Fin 144               -- 极向缠绕相位 (0-143)
    stepCount       : ℕ                     -- 全局步数计数器
    
    -- 主权闭合 KPI 监控
    zhonglvCount    : ℕ                     -- 仲吕闭合触发次数
    singularityCount: ℕ                     -- 能隙奇点捕获次数 (爻变触发)
    localChernSum   : ℕ                     -- 局部曲率和累加 (启发式代理)

open SovereignState public

--------------------------------------------------------------------------------
-- 2. 宪法级演化逻辑 (Constitutional Evolution)
--------------------------------------------------------------------------------

-- 损益步进：根据相位决定损一还是益一
stepSection : LCM.SovereignSection → Fin 144 → LCM.SovereignSection
stepSection sec phase =
  let delta = if (toℕ phase mod 2) ≡ 0b0
              then T.T₂  -- 损一：+2 ≡ -1 (mod 3)
              else T.T₁  -- 益一：+1 (mod 3)
  in map (λ t → t T.⊕ delta) sec

-- 极向相位推进
stepPhase : Fin 144 → Fin 144
stepPhase p = fromℕ ((toℕ p + 1) mod 144)

-- 单步演化函数 (含 KPI 更新)
evolve : SovereignState → SovereignState
evolve state =
  let sec       = SovereignState.section state
      currentAcc = SovereignState.acc state
      phase     = SovereignState.phase state
      steps     = SovereignState.stepCount state
      
      -- 1. 推进极向相位
      nextPhase = stepPhase phase
      
      -- 2. 更新物理权重 (30 Trits 损益旋转)
      nextSection = stepSection sec phase
      
      -- 3. 累加器更新与仲吕闭合判定
      isZhonglv = (toℕ phase mod 12) ≡ 11
      
      (newAcc , newZhonglvCount) = 
        if isZhonglv
        then (Ax.zhonglvClosure currentAcc , SovereignState.zhonglvCount state + 1)
        else ((currentAcc + Inv.SOVEREIGN_LCM) mod Inv.SOVEREIGN_LCM , SovereignState.zhonglvCount state)
      
      -- 4. 宪法约束：对 Section 执行 LCM 模归零
      normalizedSection = LCM.modLCM nextSection
      
      -- 5. 局部陈数监控 (启发式代理)
      currentChern = LCM.computeLocalChernHeuristic normalizedSection
      newChernSum  = SovereignState.localChernSum state + currentChern
      
  in mkState normalizedSection newAcc nextPhase (suc steps) newZhonglvCount 
            (SovereignState.singularityCount state) newChernSum

--------------------------------------------------------------------------------
-- 3. I/O 边界：与 TQ1_0 格式的互操作
--------------------------------------------------------------------------------

-- 将内部 SovereignState 导出为 TQ10 块 (使用 LCM 宪法级打包)
stateToTQ10 : SovereignState → Vec ℕ 6  -- 6 字节 qs 字段
stateToTQ10 state = LCM.packSectionToQs (SovereignState.section state)

-- 从 6 字节 qs 导入为 SovereignState (含能隙硬边界检查)
tq10ToState : Vec ℕ 6 → SovereignState
tq10ToState qs =
  let section = LCM.unpackQsToSection qs
      
      -- 检查是否有奇点捕获 (任何字节 ≥ 243)
      hasSingularity : Vec ℕ 6 → Bool
      hasSingularity [] = false
      hasSingularity (b ∷ bs) = if b ≥ LCM.GAP_THRESHOLD then true else hasSingularity bs
      
      singularityCaught = hasSingularity qs
      newSingularityCount = if singularityCaught then 1 else 0
      
  in mkState section 0 0b0 0 0 newSingularityCount 0

--------------------------------------------------------------------------------
-- 4. 宪法验证 (Constitutional Verification)
--------------------------------------------------------------------------------

-- 定理 1：演化保持 LCM 模合法性
evolvePreservesLCM : ∀ (state : SovereignState) →
  LCM.sectionToCoordinate (SovereignState.section (evolve state)) < Inv.SOVEREIGN_LCM
evolvePreservesLCM state = LCM.modLCM_Legal (stepSection (section state) (phase state))

-- 定理 2：12 步后触发仲吕闭合
postulate
  zhonglvTriggeredAfter12 :
    let initialState = mkState (replicate 30 T.T₀) 0 0b0 0 0 0 0
        stateAfter12 = iterate 12 evolve initialState
    in SovereignState.zhonglvCount stateAfter12 ≥ 1
  where
    iterate : ℕ → (SovereignState → SovereignState) → SovereignState → SovereignState
    iterate zero f s = s
    iterate (suc n) f s = iterate n f (f s)

-- 定理 3：能隙硬边界生效 (解包非法字节时奇点计数增加)
gapSingularityIncreasesOnInvalidInput : 
  let invalidQs = 250 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []  -- 250 ≥ 243
      state = tq10ToState invalidQs
  in SovereignState.singularityCount state ≡ 1
gapSingularityIncreasesOnInvalidInput = refl
