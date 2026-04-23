{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Engine.QsUpdate
-- 引擎层：主权块权重 (qs) 的物理更新逻辑
--
-- 核心原理：
-- 将损益操作 (Loss/Gain) 映射为 30 个 Trit 的相位旋转。
-- 通过解包 -> 旋转 -> 打包 的循环，确保主权块的物理状态
-- 严格遵循律算公理的离散拓扑演化。
--
-- 安全性：
-- 由于 Trit 的旋转是模 3 循环 (0-1-2-0...)，
-- 任何 5 个 Trit 的组合打包后必然在 0-242 范围内。
-- 因此，更新后的 qs 永远不会落入“能隙奇点捕获区” (243-255)。

module Sovereign.Engine.QsUpdate where

open import Data.Vec using (Vec; map; _∷_; [])
open import Data.Fin using (Fin; toℕ)

import Sovereign.Format.TQ10 as TQ10
import Sovereign.Base.TritOps as TritOps

open TQ10 using (TQ10Block; qs; PackedByte; pack5; unpack5)

--------------------------------------------------------------------------------
-- 1. 单元操作：单字节更新 (Single Byte Update)
--------------------------------------------------------------------------------

-- 对单个 PackedByte (5 Trits) 应用损益旋转
updateByte : TritOps.Op → PackedByte → PackedByte
updateByte op byte = 
  let trits = unpack5 byte
      -- 将 Op 应用于每个 Trit (相位旋转)
      rotated = Data.Vec.Base.map (TritOps.applyOp op) trits
  in pack5 rotated

-- 证明/注释：
-- 由于 pack5 接受任意 Vec Trit 5 并输出 Fin 243 (0-242)，
-- 且 applyOp 只是置换 Trit 值 (T-/T0/T+)，不改变 Trit 的数量，
-- 所以 updateByte 总是返回合法的 PackedByte。

--------------------------------------------------------------------------------
-- 2. 块操作：全量更新 (Block Update)
--------------------------------------------------------------------------------

-- 更新整个主权块的 qs 字段
updateQs : TritOps.Op → TQ10Block → TQ10Block
updateQs op blk = 
  let currentQs = TQ10Block.qs blk
      -- 对 6 个字节分别进行解包-旋转-打包
      newQs = Data.Vec.Base.map (updateByte op) currentQs
  in record blk { qs = newQs }

--------------------------------------------------------------------------------
-- 3. 验证 (Verification)
--------------------------------------------------------------------------------

-- 验证：对任意块执行 3 次 Loss 或 Gain 操作，qs 应恢复原状 (因为 Trit 周期为 3)
postulate
  qsCycleProperty : 
    ∀ (blk : TQ10Block) → 
    let blk1 = updateQs TritOps.Loss (updateQs TritOps.Loss (updateQs TritOps.Loss blk))
    in TQ10Block.qs blk1 ≡ TQ10Block.qs blk
