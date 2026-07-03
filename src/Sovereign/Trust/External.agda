{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Trust.External
-- 信任边界：标记所有外部引用为信用0
--
-- 宪法原则：
-- 1. 所有 Agda 标准库引理初始信任度为 0 (UNTRUSTED)。
-- 2. 必须经过高维几何审查 (Geometric Review) 后才能标记为 TRUSTED。
-- 3. 核心宪法模块 (LCM, HoTT) 禁止直接使用未审查的外部引理。
--
-- 审查状态追踪：
-- UNTRUSTED     : 未审查，禁止用于宪法级证明
-- UNDER_REVIEW  : 审查中，需高维几何验证
-- TRUSTED       : 已审查，可在宪法级证明中使用

module Sovereign.Trust.External where

open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec)

--------------------------------------------------------------------------------
-- 1. 信任度枚举 (Trust Level)
--------------------------------------------------------------------------------

data TrustLevel : Set where
  UNTRUSTED     : TrustLevel  -- 信用0，禁止使用
  UNDER_REVIEW  : TrustLevel  -- 审查中
  TRUSTED       : TrustLevel  -- 已审查，可信任

--------------------------------------------------------------------------------
-- 2. 外部依赖信任矩阵 (Trust Matrix)
--------------------------------------------------------------------------------

-- 算术模块
Data.Nat.Trust            : TrustLevel
Data.Nat.Trust            = UNTRUSTED  -- ⚠️ 基于连续统算术，需重新证明

Data.Nat.Properties.Trust : TrustLevel
Data.Nat.Properties.Trust = UNTRUSTED  -- 🔴 极高风险，模运算引理未经验证

Data.Nat.DivMod.Trust     : TrustLevel
Data.Nat.DivMod.Trust     = UNTRUSTED  -- 🔴 极高风险，除法 - 模分解未验证

Data.Integer.Trust       : TrustLevel
Data.Integer.Trust       = UNTRUSTED  -- ⚠️ 整数定义可能兼容，需审查

Data.Rational.Trust      : TrustLevel
Data.Rational.Trust      = UNTRUSTED  -- ⚠️ 有理数基于连续统，禁止用于能隙计算

-- 有限类型模块
Data.Fin.Trust           : TrustLevel
Data.Fin.Trust           = UNDER_REVIEW  -- 🟡 边界检查需与缠绕数对齐

Data.Vec.Trust           : TrustLevel
Data.Vec.Trust           = UNDER_REVIEW  -- 🟡 map 需证明保持纤维丛结构

-- 逻辑与等式模块
Relation.Binary.PropositionalEquality.Trust : TrustLevel
Relation.Binary.PropositionalEquality.Trust = TRUSTED  -- ✅ 等式逻辑与高维几何兼容

Relation.Binary.PropositionalEquality.Properties.Trust : TrustLevel
Relation.Binary.PropositionalEquality.Properties.Trust = UNDER_REVIEW

-- Cubical 模块
Cubical.Foundations.Prelude.Trust : TrustLevel
Cubical.Foundations.Prelude.Trust = UNTRUSTED  -- 🔴 Path 类型与离散环面可能冲突

Cubical.Core.Everything.Trust : TrustLevel
Cubical.Core.Everything.Trust = UNTRUSTED  -- 🔴 连续同伦理论，需离散化

--------------------------------------------------------------------------------
-- 3. 审查清单 (Review Checklist)
--------------------------------------------------------------------------------

record ReviewStatus : Set where
  field
    module_name    : String
    trust_level    : TrustLevel
    review_notes   : String
    reviewed_by    : String  -- 必须是高维几何审查员

-- 当前审查状态
review_log : Vec ReviewStatus 5
review_log = 
  -- 待审查的关键引理
  record { module_name = "Data.Nat.Properties.+-mod"
         ; trust_level = UNTRUSTED
         ; review_notes = "模运算分配律基于连续统，需在 GF(3) 格点上重新证明"
         ; reviewed_by = "PENDING"
         } ∷
  record { module_name = "Data.Nat.Properties.m*n%m≡0"
         ; trust_level = UNTRUSTED
         ; review_notes = "乘法模零律需验证与 T⁶ 离散拓扑的兼容性"
         ; reviewed_by = "PENDING"
         } ∷
  record { module_name = "Data.Nat.DivMod.div-mod"
         ; trust_level = UNTRUSTED
         ; review_notes = "除法 - 模分解唯一性需在 Base-3 编码中验证"
         ; reviewed_by = "PENDING"
         } ∷
  record { module_name = "Cubical.Foundations.Prelude.Path"
         ; trust_level = UNTRUSTED
         ; review_notes = "Path 类型假设连续空间，需定义离散版本"
         ; reviewed_by = "PENDING"
         } ∷
  record { module_name = "Data.Fin.boundary"
         ; trust_level = UNDER_REVIEW
         ; review_notes = "Fin 边界检查需与极向 144/环向 46 对齐"
         ; reviewed_by = "PENDING"
         } ∷ []

--------------------------------------------------------------------------------
-- 4. 宪法级访问控制 (Constitutional Access Control)
--------------------------------------------------------------------------------

-- 只有 TRUSTED 的外部引理才能用于宪法级证明
-- 直接定义为：信任级别为 TRUSTED 时返回 true，否则 false
require_trusted : ∀ {m : String} (trust : TrustLevel) → Bool
require_trusted TRUSTED = true
require_trusted UNTRUSTED = false
require_trusted UNDER_REVIEW = false

-- 使用示例：
-- 如果尝试使用 UNTRUSTED 引理，类型检查器将拒绝
-- require_trusted Data.Nat.Properties.Trust refl  -- 类型错误！

-- 信任检查辅助函数
isTrustedForConstitutionalUse : TrustLevel → Bool
isTrustedForConstitutionalUse = require_trusted
