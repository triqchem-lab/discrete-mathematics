{-# OPTIONS --guardedness #-}

-- | Sovereign.Projection.Binary
-- 投影链：二进制与三进制的有损降维与上下文拾起
--
-- 宪法定义：
-- 1. projectTritToBit 是有损投影 (Lossy Projection)，仅用于外部 I/O 输出。
--    T₁(平衡) → 1, T₀(吸收)/T₂(表达) → 0。
-- 2. restoreTritWithContext 必须携带 CurrentPhase 与 WuxingMask。
--    **更新**：使用“五行掩码 (WuXing Mask)”替代“相位奇偶性”进行启发式恢复。
--    这符合宪法中关于五行模数区决定能量态/手性倾向的定义。

module Sovereign.Projection.Binary where

open import Data.Fin using (Fin; toℕ; fromℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

import Sovereign.Coding.Trit as T

--------------------------------------------------------------------------------
-- 1. 二进制类型定义 (Bit)
--------------------------------------------------------------------------------

-- 二进制是 Fin 2，代表电性文明的残缺快照
Bit : Set
Bit = Fin 2

B₀ : Bit
B₀ = 0b0

B₁ : Bit
B₁ = 0b1

--------------------------------------------------------------------------------
-- 2. 上下文定义 (Context for Restoration)
--------------------------------------------------------------------------------

-- 高维上下文：决定如何从 Bit 恢复 Trit 的相位信息
record Context : Set where
  constructor mkCtx
  field
    currentPhase : Fin 144    -- 极向缠绕相位 (0-143)
    wuxingMask   : Fin 5      -- 五行模数区掩码 (0-4)

open Context public

--------------------------------------------------------------------------------
-- 3. 有损投影：Trit → Bit
--------------------------------------------------------------------------------

-- 投影规则：
-- T₀ (吸收/0) → 0
-- T₁ (平衡/1) → 1
-- T₂ (表达/2) → 0 (信息折叠！与 T₀ 无法区分)
projectTritToBit : T.Trit → Bit
projectTritToBit t with T.toℕ t
... | 0 = B₀
... | 1 = B₁
... | 2 = B₀  -- ⚠️ 拓扑信息在此丢失

--------------------------------------------------------------------------------
-- 4. 投影信息丢失证明 (Proof of Lossiness)
--------------------------------------------------------------------------------

-- 辅助：T₀ 和 T₂ 可判定不等
t0≢t2 : ¬ (T.T₀ ≡ T.T₂)
t0≢t2 with T.T₀ T.≟ T.T₂
... | no p  = p
... | yes _ = λ ()

-- 定理：投影有损 — T₀ 和 T₂ 不同，但投影到相同 Bit
projectionIsLossy : ¬ (T.T₀ ≡ T.T₂) × (projectTritToBit T.T₀ ≡ projectTritToBit T.T₂)
projectionIsLossy = t0≢t2 , refl

--------------------------------------------------------------------------------
-- 5. 上下文拾起：Bit → Trit (基于五行掩码的启发式恢复)
--------------------------------------------------------------------------------

-- ⚠️ 启发式说明：
-- 根据律算宪法，Bit 0 代表非平衡态 ({T₀, T₂})。
-- 恢复为 T₀ (吸收) 还是 T₂ (表达) 取决于当前的五行模数区 (WuXing Mask)
-- 所偏好的能量倾向。
--
-- 依据：宪法中五行基数 (Base) 的奇偶性与阴阳属性：
-- 火(2)-偶数-阴 → 偏好 T₀
-- 土(5)-奇数-阳 → 偏好 T₂
-- 金(4)-偶数-阴 → 偏好 T₀
-- 水(6)-偶数-阴 → 偏好 T₀
-- 木(8)-偶数-阴 → 偏好 T₀
--
-- 这比之前的“相位奇偶性”具有更强的理论基础。

private
  -- 五行恢复偏好表
  -- 输入：五行索引 (0=火, 1=土, 2=金, 3=水, 4=木)
  -- 输出：Bit=0 时的首选 Trit
  wuxingDefaultRecovery : Fin 5 → T.Trit
  wuxingDefaultRecovery zero = T.T₀                  -- 火 (Fire, Base 2)
  wuxingDefaultRecovery (suc zero) = T.T₂            -- 土 (Earth, Base 5)
  wuxingDefaultRecovery (suc (suc zero)) = T.T₀      -- 金 (Metal, Base 4)
  wuxingDefaultRecovery (suc (suc (suc zero))) = T.T₀-- 水 (Water, Base 6)
  wuxingDefaultRecovery (suc (suc (suc (suc zero)))) = T.T₀ -- 木 (Wood, Base 8)
  wuxingDefaultRecovery _ = T.T₀                     -- 安全回退

-- 恢复函数
restoreTritWithContext : Bit → Context → T.Trit
restoreTritWithContext b ctx =
  case b of λ where
    B₁ → T.T₁  -- Bit 1 必然恢复为平衡态 T₁
    B₀ → wuxingDefaultRecovery (Context.wuxingMask ctx) -- Bit 0 依据五行偏好恢复

--------------------------------------------------------------------------------
-- 6. 上下文恢复正确性证明 (Proof of Contextual Restoration)
--------------------------------------------------------------------------------

-- 定理：对于 T₁，无论上下文如何，只要 Bit 是 1，就能完美恢复
restoreT1Perfect : ∀ (ctx : Context) →
  restoreTritWithContext (projectTritToBit T.T₁) ctx ≡ T.T₁
restoreT1Perfect ctx = refl

-- 定理：对于 T₀，如果五行偏好是 T₀ (火/金/水/木)，则恢复正确
-- 证明：基于 wuxingDefaultRecovery 的显式定义进行情况分析
restoreT0CorrectInNonEarthRegions :
  ∀ (ctx : Context) →
  Context.wuxingMask ctx ≢ 1b1 → -- 排除土区
  restoreTritWithContext (projectTritToBit T.T₀) ctx ≡ T.T₀
restoreT0CorrectInNonEarthRegions ctx mask≢1 =
  let projBit = projectTritToBit T.T₀  -- = B₀
      restored = restoreTritWithContext B₀ ctx  -- = wuxingDefaultRecovery (wuxingMask ctx)
      mask = Context.wuxingMask ctx
  in prove mask mask≢1
  where
    prove : (m : Fin 5) → m ≢ 1b1 → wuxingDefaultRecovery m ≡ T.T₀
    prove zero _ = refl          -- 火 → T₀
    prove (suc zero) not1 = ⊥-elim (not1 refl)  -- 土 → 矛盾
    prove (suc (suc zero)) _ = refl  -- 金 → T₀
    prove (suc (suc (suc zero))) _ = refl  -- 水 → T₀
    prove (suc (suc (suc (suc zero)))) _ = refl  -- 木 → T₀
    open import Data.Empty using (⊥-elim)

-- 定理：对于 T₂，如果五行偏好是 T₂ (土区)，则恢复正确
restoreT2CorrectInEarthRegion :
  ∀ (ctx : Context) →
  Context.wuxingMask ctx ≡ 1b1 → -- 仅限土区
  restoreTritWithContext (projectTritToBit T.T₂) ctx ≡ T.T₂
restoreT2CorrectInEarthRegion ctx mask≡1 =
  let projBit = projectTritToBit T.T₂  -- = B₀
      restored = restoreTritWithContext B₀ ctx  -- = wuxingDefaultRecovery (wuxingMask ctx)
      mask = Context.wuxingMask ctx
  in prove mask mask≡1
  where
    prove : (m : Fin 5) → m ≡ 1b1 → wuxingDefaultRecovery m ≡ T.T₂
    prove zero eq = ⊥-elim (injective-zero eq)  -- 火 ≠ 土
    prove (suc zero) _ = refl  -- 土 → T₂
    prove (suc (suc zero)) eq = ⊥-elim (injective-suc eq)  -- 金 ≠ 土
    prove (suc (suc (suc zero))) eq = ⊥-elim (injective-suc eq)  -- 水 ≠ 土
    prove (suc (suc (suc (suc zero)))) eq = ⊥-elim (injective-suc eq)  -- 木 ≠ 土

    injective-zero : {n : ℕ} → 0b0 ≡ suc n → ⊥
    injective-zero ()

    injective-suc : {n m : ℕ} → suc n ≡ suc m → n ≡ m → ⊥
    injective-suc {_} {zero} () _
    injective-suc {zero} {suc _} refl _
    injective-suc {suc _} {suc _} refl _ = refl

    open import Data.Empty using (⊥-elim)
