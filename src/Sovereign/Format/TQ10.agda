{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Format.TQ10
-- 格式定义：主权 TQ1_0 格式 (16 字节主权块)
--
-- 核心概念：
-- 主权块是高维拓扑状态在二维硅基介质上的**物理投影**。
-- 它将 30 个 GF(3) Trit (逻辑态) 压缩存储，并携带拓扑控制信息。
--
-- 宪法约束：
-- 1. 禁止浮点：所有字段必须是整数或位域。
-- 2. 奇点捕获：字节值 243-255 为能隙奇点 (Gap Singularity)，非法。
-- 3. 16 字节对齐：对应 128 位全息通道。

module Sovereign.Format.TQ10 where

open import Data.Nat using (ℕ; _+_; _*_; _<_; _≥_; _mod_; _div_)
open import Data.Fin using (Fin; toℕ; fromℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)

import Sovereign.Base.Trit as Trit
import Sovereign.Base.Invariants as Inv
import Sovereign.Geometry.Tryte as TryteGeom -- Import geometric definition

--------------------------------------------------------------------------------
-- 1. 基础存储单元 (Storage Units)
--------------------------------------------------------------------------------

-- 逻辑单元：Tryte (6 Trits = 729 态)
-- 这是主权状态机运算的最小完整截面
-- 引用几何定义：T⁶ 单点纤维截面
Tryte : Set
Tryte = TryteGeom.Tryte

-- 物理存储单元：PackedByte (5 Trits = 243 态)
-- 1 字节 = 8 bits. 3^5 = 243 < 256.
-- 剩余 13 个状态 (243-255) 为“能隙奇点捕获区”
PackedByte : Set
PackedByte = Fin 243

-- 验证字节合法性 (是否在奇点捕获区之外)
isPackedValid : Fin 256 → Bool
isPackedValid byte with toℕ byte
... | n = n < 243

--------------------------------------------------------------------------------
-- 2. 打包与解包逻辑 (Packing Logic)
--------------------------------------------------------------------------------

-- 将 6 Trits (Tryte) 转换为 32-bit 整数用于中间处理
-- 然后切分为 5-trit 的 PackedBytes
-- 
-- 映射规则 (TQ1_0 规范):
-- 30 Trits (逻辑) <-> 6 Bytes (物理)
-- 这是一个跨维度的投影过程。

-- 辅助：将单个 Trit 映射为 Base-3 数字 {0, 1, 2}
tritToBase3 : Trit.Trit → ℕ
tritToBase3 Trit.T- = 0
tritToBase3 Trit.T0 = 1
tritToBase3 Trit.T+ = 2

-- 辅助：将 Base-3 数字还原为 Trit
base3ToTrit : ℕ → Trit.Trit
base3ToTrit 0 = Trit.T-
base3ToTrit 1 = Trit.T0
base3ToTrit 2 = Trit.T+
base3ToTrit _ = Trit.T0 -- 默认平衡

-- 打包 5 Trits 到 1 PackedByte
pack5 : Vec Trit.Trit 5 → PackedByte
pack5 (t0 ∷ t1 ∷ t2 ∷ t3 ∷ t4 ∷ []) =
  let v0 = tritToBase3 t0
      v1 = tritToBase3 t1
      v2 = tritToBase3 t2
      v3 = tritToBase3 t3
      v4 = tritToBase3 t4
      -- Base-3 to Int: v0 + v1*3 + v2*9 + v3*27 + v4*81
      val = v0 + (v1 * 3) + (v2 * 9) + (v3 * 27) + (v4 * 81)
  in fromℕ val

-- 解包 1 PackedByte 到 5 Trits
unpack5 : PackedByte → Vec Trit.Trit 5
unpack5 byte = 
  let val = toℕ byte
      v0 = val mod 3
      v1 = (val div 3) mod 3
      v2 = (val div 9) mod 3
      v3 = (val div 27) mod 3
      v4 = (val div 81) mod 3
  in base3ToTrit v0 ∷ 
     base3ToTrit v1 ∷ 
     base3ToTrit v2 ∷ 
     base3ToTrit v3 ∷ 
     base3ToTrit v4 ∷ []

--------------------------------------------------------------------------------
-- 3. 主权块定义 (Sovereign Block Definition)
--------------------------------------------------------------------------------

-- TQ1_0 16 字节块结构
record TQ10Block : Set where
  constructor mkBlock
  field
    -- 存储层：30 trit 权重 (6 字节)
    -- 对应 5 个逻辑 Tryte (火、土、金、水、木)
    qs          : Vec PackedByte 6  
    
    -- 校验层：拓扑守门人
    scale       : Fin 256           -- UE8M0 主权尺度指数
    phase_bias  : Fin 256           -- 高 4 位: 极向相位(0-11), 低 4 位: C3 内部相位
    chern_guard : Fin 256           -- 高 3 位: 七阶段, 低 5 位: 局部陈数 (0-31)
    wuxing_mask : Fin 256           -- 高 5 位: 球谐方向, 低 3 位: A4 生成元

    -- 预留层：扩展
    reserved    : Vec (Fin 256) 6

open TQ10Block public

--------------------------------------------------------------------------------
-- 4. 工程约束验证 (Engineering Constraints)
--------------------------------------------------------------------------------

-- 验证块是否完整 (所有字节都在合法范围内)
isBlockValid : TQ10Block → Bool
isBlockValid blk = 
  let qs_valid = foldr (λ b acc → isPackedValid (fromℕ (toℕ b)) && acc) true (qs blk)
      -- 其他字段通常在 Fin 256 内，天然合法，除了特定的位域约束
  in qs_valid -- 简化验证，主要检查 qs 是否落入奇点捕获区

-- 提取极向相位 (Phase Bias High 4 bits)
getPolarPhase : TQ10Block → Fin 16 -- 0-15, 有效 0-11
getPolarPhase blk = 
  let pb = toℕ (phase_bias blk)
      phase = (pb div 16) mod 16
  in fromℕ phase

-- 提取局部陈数 (Chern Guard Low 5 bits)
getLocalChern : TQ10Block → Fin 32
getLocalChern blk = 
  let cg = toℕ (chern_guard blk)
      chern = cg mod 32
  in fromℕ chern
