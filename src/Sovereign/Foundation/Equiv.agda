{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Foundation.Equiv
-- 通用等价关系 record（to/from + 往返恒等）——基座接口件。
--
-- 数学背景：A ≃ B = 双向映射 + 两侧往返恒等（同构数据的最小承载）。
-- 原定义居 Structology/PlatonicTorusProjection（深度层），被 Foundation/Finiteness 族
-- 引用（Dedekind/Foundations）——波 2-C 接口抽取上提至基座层（小样#1 FirstHit 同款），
-- PlatonicTorusProjection 改引本件（其 platonicProjectionEquiv : Fin 144 ≃ … API 不变）。
--
-- 核心原则：
--   1. 本件是纯接口（无实例、无定理）——presentation 最小性：仅承载同构数据四字段；
--   2. 导出性质（单射/满射推论等）不入字段，消费侧自行导出。
--
-- 包含：_≃_（等价 record）

module Sovereign.Foundation.Equiv where

open import Relation.Binary.PropositionalEquality using (_≡_)

infix 4 _≃_

record _≃_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    to-from : ∀ b → to (from b) ≡ b
    from-to : ∀ a → from (to a) ≡ a
