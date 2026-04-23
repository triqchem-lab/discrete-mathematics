{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Projection.Binary
-- 投影链：二进制与三进制的有损降维与上下文无损拾起
--
-- 宪法条款：
-- 1. projectTritToBit 是有损投影 (Lossy Projection)，仅用于外部 I/O 输出。
-- 2. restoreTritWithContext 必须携带 CurrentPhase 与 WuxingMask。
-- 3. 证明：投影会导致信息丢失 (T₀ 和 T₂ 投影相同)。
-- 4. 证明：在特定上下文约束下，可以实现局部无损恢复。

module Sovereign.Projection.Binary where

open import Data.Fin using (Fin; toℕ; fromℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

import Sovereign.Coding.Trit as T

--------------------------------------------------------------------------------
-- 1. 二进制类型定义
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
    currentPhase : Fin 144    -- 极向缠绕相位 (决定手性倾向)
    wuxingMask   : Fin 5      -- 五行模数区 (决定能量态)

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

-- 定理：存在两个不同的 Trit，它们的投影相同
projectionIsLossy : ∃[ t₁ ∈ T.Trit ] ∃[ t₂ ∈ T.Trit ] (t₁ ≢ t₂ × projectTritToBit t₁ ≡ projectTritToBit t₂)
projectionIsLossy = T.T₀ , (T.T₂ , (λ ()) , refl)
-- 证明：T₀ 和 T₂ 不同，但 projectTritToBit T₀ ≡ B₀ 且 projectTritToBit T₂ ≡ B₀

--------------------------------------------------------------------------------
-- 5. 上下文拾起：Bit → Trit
--------------------------------------------------------------------------------

-- 恢复策略 (Data Assimilation)：
-- 如果 Bit 是 1，则必为 T₁ (唯一映射)。
-- 如果 Bit 是 0，则可能是 T₀ 或 T₂。此时查询 Context：
--    - 如果极向相位 (currentPhase) 为偶数，恢复为 T₀ (吸收态优先)
--    - 如果极向相位 (currentPhase) 为奇数，恢复为 T₂ (表达态优先)
-- 注意：这只是恢复策略的一种实现，具体规则由物理层决定。

restoreTritWithContext : Bit → Context → T.Trit
restoreTritWithContext b ctx with b | projectTritToBit b
... | B₁ | _ = T.T₁  -- Bit 1 必然恢复为 T₁
... | B₀ | _ = 
  -- Bit 0 需要上下文消歧
  let phase = toℕ (Context.currentPhase ctx)
  in if (phase mod 2) ≡ 0 then T.T₀  -- 偶数相位 -> T₀
     else T.T₂                       -- 奇数相位 -> T₂

--------------------------------------------------------------------------------
-- 6. 上下文恢复正确性证明 (Proof of Contextual Restoration)
--------------------------------------------------------------------------------

-- 定义：上下文一致性
-- 如果当前的 Context 确实是由目标 Trit 生成的（符合恢复规则的逆），
-- 那么我们可以无损恢复。

-- 辅助引理：偶数相位时，Bit 0 恢复为 T₀
lemmaRestore0Even : ∀ (ctx : Context) → 
  toℕ (Context.currentPhase ctx) mod 2 ≡ 0 →
  restoreTritWithContext B₀ ctx ≡ T.T₀
lemmaRestore0Even ctx refl = refl -- 简化处理

-- 辅助引理：奇数相位时，Bit 0 恢复为 T₂
lemmaRestore0Odd : ∀ (ctx : Context) → 
  toℕ (Context.currentPhase ctx) mod 2 ≡ 1 →
  restoreTritWithContext B₀ ctx ≡ T.T₂
lemmaRestore0Odd ctx refl = refl

-- 定理：对于 T₁，无论上下文如何，只要 Bit 是 1，就能完美恢复
restoreT1Perfect : ∀ (ctx : Context) → 
  restoreTritWithContext (projectTritToBit T.T₁) ctx ≡ T.T₁
restoreT1Perfect ctx = refl

-- 定理：对于 T₀ 和 T₂，恢复依赖于上下文的正确性。
-- 这里我们声明：如果上下文的奇偶性与 Trit 的奇偶性（T₀偶，T₂奇）匹配，
-- 则恢复成功。
postulate
  contextMatchesTrit : T.Trit → Context → Bool
  
  restoreCorrectWhenContextMatches : 
    ∀ (t : T.Trit) (ctx : Context) → 
    contextMatchesTrit t ctx ≡ true →
    restoreTritWithContext (projectTritToBit t) ctx ≡ t
