{-# OPTIONS --rewriting --cubical --guardedness #-}

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

--
-- 核心原则：
--   1. 状态机/工具层——工具类型不升公理（Pgm 判据）
--   2. 编码双射件为构造性数据，断言面如实标注
--
-- 包含：（重导/声明件——正文即清单）
module Sovereign.Engine.QsUpdate where

open import Data.Vec using (Vec; map; _∷_; [])
open import Data.Fin using (Fin; zero; suc; combine; remQuot)
open import Data.Fin.Properties using (remQuot-combine; combine-remQuot)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; cong₂; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

import Sovereign.Application.TQ10 as TQ10
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

-- 3.1 TQ10.finToTrit 和 TQ10.tritToFin 在 Fin 3 上互逆

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

  -- pack5 / unpack5 互逆性（2026-10-11 构造化闭合——原「纯机械展开」公设已实施，postulate -2）
  --
  -- 原理（不变）：
  -- - pack5∘unpack5 由 combine-remQuot {81} 3 b 逐层展开保证
  -- - unpack5∘pack5 由 remQuot-combine i j 逐层展开保证
  -- 施工形：转换辅助件（p 元组显式参数 + 等式假设——refl 形自证）+
  -- 显式项链（每步 cong/trans 落在写出的项上，绕开 with-abstraction 的语法匹配盲区）。

  -- 五位合并形（pack5 的 combine 嵌套——定义等价）
  comb5 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → PackedByte
  comb5 x4 x3 x2 x1 x0 = combine (combine (combine (combine x4 x3) x2) x1) x0

  -- 五位同变（变量侧 refl 形自证）
  cong5-comb5 : {a4 b4 a3 b3 a2 b2 a1 b1 a0 b0 : Fin 3}
    → a4 ≡ b4 → a3 ≡ b3 → a2 ≡ b2 → a1 ≡ b1 → a0 ≡ b0
    → comb5 a4 a3 a2 a1 a0 ≡ comb5 b4 b3 b2 b1 b0
  cong5-comb5 refl refl refl refl refl = refl

  -- 合并链（四层 combine-remQuot 上行——3 层 trans 达界）
  merge4 : (p4 : Fin 3 × Fin 3) (p3 : Fin 9 × Fin 3) (p2 : Fin 27 × Fin 3) (p1 : Fin 81 × Fin 3)
           (b : PackedByte)
    → uncurry combine p4 ≡ proj₁ p3
    → uncurry combine p3 ≡ proj₁ p2
    → uncurry combine p2 ≡ proj₁ p1
    → uncurry combine p1 ≡ b
    → comb5 (proj₁ p4) (proj₂ p4) (proj₂ p3) (proj₂ p2) (proj₂ p1) ≡ b
  merge4 p4 p3 p2 p1 b e4 e3 e2 e1 =
    trans (cong (λ z → combine (combine (combine z (proj₂ p3)) (proj₂ p2)) (proj₂ p1)) e4)
     (trans (cong (λ z → combine (combine z (proj₂ p2)) (proj₂ p1)) e3)
      (trans (cong (λ z → combine z (proj₂ p1)) e2) e1))

  -- 解包向量逐位提升（位等式入参 + cong₂ 链——零 pattern 消去）
  unp-lift2 : (p1 : Fin 81 × Fin 3) (p2 : Fin 27 × Fin 3) (p3 : Fin 9 × Fin 3) (p4 : Fin 3 × Fin 3)
              (v0 v1 v2 v3 v4 : Trit.Trit)
    → proj₂ p1 ≡ TQ10.tritToFin v0
    → proj₂ p2 ≡ TQ10.tritToFin v1
    → proj₂ p3 ≡ TQ10.tritToFin v2
    → proj₂ p4 ≡ TQ10.tritToFin v3
    → proj₁ p4 ≡ TQ10.tritToFin v4
    → TQ10.finToTrit (proj₂ p1) ∷ TQ10.finToTrit (proj₂ p2) ∷ TQ10.finToTrit (proj₂ p3)
        ∷ TQ10.finToTrit (proj₂ p4) ∷ TQ10.finToTrit (proj₁ p4) ∷ []
      ≡ v0 ∷ v1 ∷ v2 ∷ v3 ∷ v4 ∷ []
  unp-lift2 _ _ _ _ v0 v1 v2 v3 v4 e0 e1 e2 e3 e4 =
    cong₂ _∷_ (trans (cong TQ10.finToTrit e0) (finToTrit∘tritToFin v0))
     (cong₂ _∷_ (trans (cong TQ10.finToTrit e1) (finToTrit∘tritToFin v1))
      (cong₂ _∷_ (trans (cong TQ10.finToTrit e2) (finToTrit∘tritToFin v2))
       (cong₂ _∷_ (trans (cong TQ10.finToTrit e3) (finToTrit∘tritToFin v3))
        (cong₂ _∷_ (trans (cong TQ10.finToTrit e4) (finToTrit∘tritToFin v4)) refl))))

  -- 主件：unpack5∘pack5（分层穿透位等式 + 五位 finToTrit∘tritToFin 消去）
  unpack5∘pack5 : ∀ (v : Vec Trit.Trit 5) → unpack5 (pack5 v) ≡ v
  unpack5∘pack5 (v0 ∷ v1 ∷ v2 ∷ v3 ∷ v4 ∷ []) =
    unp-lift2 (remQuot {m = 81} 3 N0)
      (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 N0)))
      (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 N0)))))
      (remQuot {m = 3} 3 (proj₁ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 N0)))))))
      v0 v1 v2 v3 v4 bit0 bit1 bit2 bit3 bit4
    where
    tv0 = TQ10.tritToFin v0; tv1 = TQ10.tritToFin v1; tv2 = TQ10.tritToFin v2
    tv3 = TQ10.tritToFin v3; tv4 = TQ10.tritToFin v4
    N3 = combine tv4 tv3
    N2 = combine N3 tv2
    N1 = combine N2 tv1
    N0 = combine N1 tv0
    -- 四层 remQuot-combine 锚等式
    e0 : remQuot {m = 81} 3 N0 ≡ (N1 , tv0)
    e0 = remQuot-combine N1 tv0
    e1 : remQuot {m = 27} 3 N1 ≡ (N2 , tv1)
    e1 = remQuot-combine N2 tv1
    e2 : remQuot {m = 9} 3 N2 ≡ (N3 , tv2)
    e2 = remQuot-combine N3 tv2
    e3 : remQuot {m = 3} 3 N3 ≡ (tv4 , tv3)
    e3 = remQuot-combine tv4 tv3
    -- 分位等式：分层动机穿透（每步 cong 穿透外层粘住的 proj₁ (remQuot …)）
    bit0 : proj₂ (remQuot {m = 81} 3 N0) ≡ tv0
    bit0 = cong proj₂ e0
    bit1 : proj₂ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 N0))) ≡ tv1
    bit1 = trans (cong (λ z → proj₂ (remQuot {m = 27} 3 (proj₁ z))) e0) (cong proj₂ e1)
    bit2 : proj₂ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 N0))))) ≡ tv2
    bit2 = trans (cong (λ z → proj₂ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ z))))) e0)
            (trans (cong (λ z → proj₂ (remQuot {m = 9} 3 (proj₁ z))) e1) (cong proj₂ e2))
    -- 4 层穿透（唯一超 3 trans 处——分层动机链不可拆，L2 例外论证）
    bit3 : proj₂ (remQuot {m = 3} 3 (proj₁ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 N0))))))) ≡ tv3
    bit3 = trans (cong (λ z → proj₂ (remQuot {m = 3} 3 (proj₁ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ z))))))) e0)
            (trans (cong (λ z → proj₂ (remQuot {m = 3} 3 (proj₁ (remQuot {m = 9} 3 (proj₁ z))))) e1)
             (trans (cong (λ z → proj₂ (remQuot {m = 3} 3 (proj₁ z))) e2) (cong proj₂ e3)))
    bit4 : proj₁ (remQuot {m = 3} 3 (proj₁ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 N0))))))) ≡ tv4
    bit4 = trans (cong (λ z → proj₁ (remQuot {m = 3} 3 (proj₁ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ z))))))) e0)
            (trans (cong (λ z → proj₁ (remQuot {m = 3} 3 (proj₁ (remQuot {m = 9} 3 (proj₁ z))))) e1)
             (trans (cong (λ z → proj₁ (remQuot {m = 3} 3 (proj₁ z))) e2) (cong proj₁ e3)))

  -- 主件：pack5∘unpack5（五位 tritToFin∘finToTrit 消去 + 四层 combine-remQuot 合并）
  pack5∘unpack5 : ∀ (b : PackedByte) → pack5 (unpack5 b) ≡ b
  pack5∘unpack5 b =
    trans (cong5-comb5
      (tritToFin∘finToTrit (proj₁ (remQuot {m = 3} 3 (proj₁ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 b)))))))))
      (tritToFin∘finToTrit (proj₂ (remQuot {m = 3} 3 (proj₁ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 b)))))))))
      (tritToFin∘finToTrit (proj₂ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 b)))))))
      (tritToFin∘finToTrit (proj₂ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 b)))))
      (tritToFin∘finToTrit (proj₂ (remQuot {m = 81} 3 b))))
     (merge4
      (remQuot {m = 3} 3 (proj₁ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 b)))))))
      (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 b)))))
      (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 b)))
      (remQuot {m = 81} 3 b)
      b
      (combine-remQuot 3 (proj₁ (remQuot {m = 9} 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 b)))))))
      (combine-remQuot 3 (proj₁ (remQuot {m = 27} 3 (proj₁ (remQuot {m = 81} 3 b)))))
      (combine-remQuot 3 (proj₁ (remQuot {m = 81} 3 b)))
      (combine-remQuot 3 b))

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
