{-# OPTIONS --rewriting --cubical --guardedness #-}

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

--
-- 核心原则：
--   1. 数学内容优先（背景→定义→引理→定理），证明每步可读；
--   2. 具名引理 + ∙/trans 链默认 ≤3 层；零洞零 postulate 目标；
--   3. 六段式分层：①头 ②导入 ③基础件 ④主引理 ⑤组合层 ⑥核对层。
--
-- 包含：Tryte、PackedByte、isPackedValid、tritToBase3、base3ToTrit、tritToFin

module Sovereign.Format.TQ10 where

open import Data.Nat using (ℕ; _+_; _*_; _<_; _≥_; _<ᵇ_)
open import Data.Nat.DivMod using (_mod_; _div_)
open import Data.Fin using (Fin; toℕ; fromℕ; combine; remQuot; #_)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import Sovereign.Base.Trit as Trit
import Sovereign.Base.Invariants as Inv
import Sovereign.Geometry.Tryte as TryteGeom -- Import geometric definition

--------------------------------------------------------------------------------
-- 1. 基础存储单元 (Storage Units)
--------------------------------------------------------------------------------

-- 逻辑单元：Tryte (6 Trits = 729 态)
-- 这是主权状态机运算的最小完整截面
-- 引用几何定义：T⁶ 单点纤维截面
-- ──────────────────────────────────────────────
-- ③ 基础件层 / ④ 主引理层（具名引理，∙ 链 ≤3）
-- ──────────────────────────────────────────────
Tryte : Set
Tryte = TryteGeom.Tryte

-- 物理存储单元：PackedByte (5 Trits = 243 态)
-- 1 字节 = 8 bits. 3^5 = 243 < 256.
-- 剩余 13 个状态 (243-255) 为“能隙奇点捕获区”
PackedByte : Set
PackedByte = Fin 243

-- 验证字节合法性 (是否在奇点捕获区之外)
isPackedValid : PackedByte → Bool
isPackedValid byte = toℕ byte <ᵇ 243

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
tritToBase3 Trit.T₀ = 0
tritToBase3 Trit.T₁ = 1
tritToBase3 Trit.T₂ = 2

-- 辅助：将 Base-3 数字还原为 Trit
base3ToTrit : ℕ → Trit.Trit
base3ToTrit 0 = Trit.T₀
base3ToTrit 1 = Trit.T₁
base3ToTrit 2 = Trit.T₂
base3ToTrit _ = Trit.T₁ -- 默认平衡

-- Trit 与 Fin 3 的双向转换 (用于 combine/remQuot 打包)
tritToFin : Trit.Trit → Fin 3
tritToFin Trit.T₀ = # 0
tritToFin Trit.T₁ = # 1
tritToFin Trit.T₂ = # 2

finToTrit : Fin 3 → Trit.Trit
finToTrit x with toℕ x
... | 0 = Trit.T₀
... | 1 = Trit.T₁
... | 2 = Trit.T₂
... | _ = Trit.T₁ -- unreachable for Fin 3

-- 打包 5 Trits 到 1 PackedByte
-- 使用 combine (标准库的混合进制编码) 将 5 个 Fin 3 压缩为 Fin 243
pack5 : Vec Trit.Trit 5 → PackedByte
pack5 (v0 ∷ v1 ∷ v2 ∷ v3 ∷ v4 ∷ []) =
  combine (combine (combine (combine tv4 tv3) tv2) tv1) tv0
  where
  tv0 = tritToFin v0; tv1 = tritToFin v1; tv2 = tritToFin v2
  tv3 = tritToFin v3; tv4 = tritToFin v4

-- 解包 1 PackedByte 到 5 Trits
-- 使用 remQuot (标准库的混合进制解码) 反向提取 5 个 Fin 3
unpack5 : PackedByte → Vec Trit.Trit 5
unpack5 byte =
  finToTrit v0-fin ∷ finToTrit v1-fin ∷ finToTrit v2-fin
    ∷ finToTrit v3-fin ∷ finToTrit v4-fin ∷ []
  where
  -- 透明 proj 形（2026-10-11）：pattern-let 会以 with 形卡住归约面，
  -- 互逆律（QsUpdate pack5∘unpack5 系）需要 remQuot 链显式可见——语义与原 let 形逐值相同
  p1 = remQuot {m = 81} 3 byte
  p2 = remQuot {m = 27} 3 (proj₁ p1)
  p3 = remQuot {m = 9}  3 (proj₁ p2)
  p4 = remQuot {m = 3}  3 (proj₁ p3)
  v0-fin = proj₂ p1
  v1-fin = proj₂ p2
  v2-fin = proj₂ p3
  v3-fin = proj₂ p4
  v4-fin = proj₁ p4

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
open TQ10Block

--------------------------------------------------------------------------------
-- 4. 工程约束验证 (Engineering Constraints)
--------------------------------------------------------------------------------

-- 验证块是否完整 (所有字节都在合法范围内)
isBlockValid : TQ10Block → Bool
isBlockValid (mkBlock qs _ _ _ _ _) = allValid qs
  where
    allValid : Vec PackedByte 6 → Bool
    allValid (x ∷ y ∷ z ∷ w ∷ u ∷ v ∷ []) =
      isPackedValid x ∧ isPackedValid y ∧ isPackedValid z ∧
      isPackedValid w ∧ isPackedValid u ∧ isPackedValid v

-- 提取极向相位 (Phase Bias High 4 bits)
-- Polar phase = high 4 bits (bits 4-7) = (toℕ phase_bias / 16) % 16
getPolarPhase : TQ10Block → Fin 16
getPolarPhase blk = ((toℕ (phase_bias blk)) div 16) mod 16

-- 提取局部陈数 (Chern Guard Low 5 bits)
-- Local Chern = low 5 bits = toℕ chern_guard % 32
getLocalChern : TQ10Block → Fin 32

-- ──────────────────────────────────────────────
-- ⑤ 组合层（主定理/装配收口）
-- ──────────────────────────────────────────────
getLocalChern blk = (toℕ (chern_guard blk)) mod 32
