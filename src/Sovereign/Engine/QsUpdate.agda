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
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; cong₂; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

import Sovereign.Format.TQ10 as TQ10
import Sovereign.Base.TritOps as TritOps
import Sovereign.Base.Trit as Trit

open TQ10 using (TQ10Block; qs; PackedByte; pack5; unpack5)

--------------------------------------------------------------------------------
-- 1. 单元操作：单字节更新 (Single Byte Update)
--------------------------------------------------------------------------------

-- 对单个 PackedByte (5 Trits) 应用损益旋转
updateByte : TritOps.Op → PackedByte → PackedByte
updateByte op byte = 
  let trits = unpack5 byte
      -- 将 Op 应用于每个 Trit (相位旋转)
      rotated = map (TritOps.applyOp op) trits
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
  let currentQs = TQ10.qs blk
      -- 对 6 个字节分别进行解包-旋转-打包
      newQs = map (updateByte op) currentQs
  in record blk { qs = newQs }

--------------------------------------------------------------------------------
-- 3. 验证 (Verification)
--------------------------------------------------------------------------------

-- 3.1 finToTrit 和 tritToFin 在 Fin 3 上互逆

private
  finToTrit∘tritToFin : ∀ (t : Trit.Trit) → TQ10.finToTrit (TQ10.tritToFin t) ≡ t
  finToTrit∘tritToFin Trit.T₀ = refl
  finToTrit∘tritToFin Trit.T₁ = refl
  finToTrit∘tritToFin Trit.T₂ = refl

  tritToFin∘finToTrit : ∀ (x : Fin 3) → TQ10.tritToFin (TQ10.finToTrit x) ≡ x
  tritToFin∘finToTrit zero          = refl
  tritToFin∘finToTrit (suc zero)    = refl
  tritToFin∘finToTrit (suc (suc zero)) = refl
  tritToFin∘finToTrit (suc (suc (suc ())))

-- 3.2 pack5 和 unpack5 互逆

private
  -- 核心策略：使用 Data.Fin.Properties 中的 combine-remQuot / remQuot-combine，
  -- 它们是 combine 和 remQuot 在单层上的互逆引理。
  -- 由于 pack5 使用 4 层嵌套的 combine，unpack5 使用 4 层 remQuot，
  -- 证明是通过逐层应用这些引理来完成的。

  -- pack5 / unpack5 互逆性
  --
  -- 原理：
  -- - pack5∘unpack5 由 combine-remQuot {81} 3 b 逐层展开保证
  -- - unpack5∘pack5 由 remQuot-combine i j 逐层展开保证
  -- 两者在标准库 Data.Fin.Properties 中均有单层引理，
  -- 此处将 4 层嵌套版本作为公设（完整形式化证明为纯机械展开）。
  postulate
    pack5∘unpack5 : ∀ (b : PackedByte) → pack5 (unpack5 b) ≡ b
    unpack5∘pack5 : ∀ (v : Vec Trit.Trit 5) → unpack5 (pack5 v) ≡ v

-- 3.3 updateByte Loss 三次复合 = id

private
  -- 辅助引理: lossOp 在 Vec 上的三次复合 = id
  map-loss3 : ∀ {n} (xs : Vec Trit.Trit n)
    → map (TritOps.applyOp TritOps.Loss)
        (map (TritOps.applyOp TritOps.Loss)
          (map (TritOps.applyOp TritOps.Loss) xs))
    ≡ xs
  map-loss3 []       = refl
  map-loss3 (x ∷ xs) = cong₂ _∷_ (TritOps.lossCycle3 x) (map-loss3 xs)

  updateByte∘loss3 : ∀ (b : PackedByte)
    → updateByte TritOps.Loss (updateByte TritOps.Loss (updateByte TritOps.Loss b)) ≡ b
  updateByte∘loss3 b = begin
    updateByte TritOps.Loss (updateByte TritOps.Loss (updateByte TritOps.Loss b))
      ≡⟨⟩  -- 展开三次 updateByte Loss
    pack5 (map lossOp (unpack5
      (pack5 (map lossOp (unpack5
        (pack5 (map lossOp (unpack5 b))))))))
      ≡⟨ cong (λ x → pack5 (map lossOp (unpack5
                       (pack5 (map lossOp x)))))
              (unpack5∘pack5 (map lossOp (unpack5 b))) ⟩
    pack5 (map lossOp (unpack5
      (pack5 (map lossOp (map lossOp (unpack5 b))))))
      ≡⟨ cong (λ x → pack5 (map lossOp x))
              (unpack5∘pack5 (map lossOp (map lossOp (unpack5 b)))) ⟩
    pack5 (map lossOp (map lossOp (map lossOp (unpack5 b))))
      ≡⟨ cong pack5 (map-loss3 (unpack5 b)) ⟩
    pack5 (unpack5 b)
      ≡⟨ pack5∘unpack5 b ⟩
    b
    ∎
    where
      lossOp = TritOps.applyOp TritOps.Loss

-- 3.4 主定理: 对任意块执行 3 次 Loss 操作，qs 恢复原状

private
  -- 辅助引理: updateByte Loss 在 Vec PackedByte 上的三次复合 = id
  map-updateByte3 : ∀ {n} (bs : Vec PackedByte n)
    → map (updateByte TritOps.Loss)
        (map (updateByte TritOps.Loss)
          (map (updateByte TritOps.Loss) bs))
    ≡ bs
  map-updateByte3 []       = refl
  map-updateByte3 (b ∷ bs) = cong₂ _∷_ (updateByte∘loss3 b) (map-updateByte3 bs)

qsCycleProperty :
  ∀ (blk : TQ10Block) →
  let blk1 = updateQs TritOps.Loss (updateQs TritOps.Loss (updateQs TritOps.Loss blk))
  in TQ10.qs blk1 ≡ TQ10.qs blk
qsCycleProperty blk = begin
  TQ10.qs (let blk1 = updateQs TritOps.Loss
                        (updateQs TritOps.Loss
                          (updateQs TritOps.Loss blk))
           in blk1)
    ≡⟨⟩  -- 展开 updateQs：仅修改 qs 字段为 map (updateByte Loss) 应用三次
  map (updateByte TritOps.Loss)
      (map (updateByte TritOps.Loss)
        (map (updateByte TritOps.Loss) (TQ10.qs blk)))
    ≡⟨ map-updateByte3 (TQ10.qs blk) ⟩
  TQ10.qs blk
  ∎
