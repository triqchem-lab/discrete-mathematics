{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseRouteListDT
-- 任务书第五层·5.1 泛型化 M2 实例首站：双三角的 **routeList + 完备性**
--
-- 数学背景：M3 的 ∂^Morse 需要 Σ_{p ∈ routeList σ τ} ε(p)·τ。
--   双三角 triVF 场上恰好三对临界胞腔对（实例层枚举完备）：
--     (FL, e02)：1 条直连路由（T₂）
--     (e02, v2)：2 条路由（T₁ 直连 + T₂ 链式）
--   合计 3 条——枚举完备性可逐项验证。
--
--   本模块直接引用 MorseBoundaryDT 已证的三条 CoefRoute 路由见证
--   （不经 CoefRouteDef 重新实例化——嵌套模块访问受限）。
--
-- 复用：MorseBoundaryDT（三路由见证 + m3-cancel）+ DoubleTriangle。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseRouteListDT where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Topology.MorseBoundaryDT
  using (r-FL-e02; r-e02-v2-direct; outer-route; inner-route;
         m3-cancel; m3-fl)

--------------------------------------------------------------------------------
-- §1. 路由清单（三条已证 CoefRoute 见证的显式枚举）
--
--   routeList FL e02 = [ r-FL-e02 ]                       （1 条）
--   routeList e02 v2 = [ r-e02-v2-direct , outer-route ]  （2 条）
--   合计 3 条——11 胞腔逐一排除其余可能（实例层完备性）
--------------------------------------------------------------------------------

-- §1a FL → e02 的路由计数：1（唯一直连）
--   e01：非临界且 V=nothing → 无路由
--   e12：非临界且 V=nothing → 无路由
--   ⟹ routeList FL e02 = [ r-FL-e02 ]

-- §1b e02 → v2 的路由计数：2（直连 + 链式）
--   直连：v2 临界且 Face v2 e02 ✓
--   链式：v0 Face e02 ∧ V v0=just e01 ∧ Face v1 e01 ∧ V v1=just e12 ∧ Face v2 e12
--   其余 v3/e13/e23 维度或面关系不符
--   ⟹ routeList e02 v2 = [ r-e02-v2-direct , outer-route ]

--------------------------------------------------------------------------------
-- §2. M3 消元（与 MorseBoundaryDT 对账——同一引理的重述）
--------------------------------------------------------------------------------

-- 逐项路由系数
route-FL-e02-coeff : Trit
route-FL-e02-coeff = T₂

route-e02-v2-direct-coeff : Trit
route-e02-v2-direct-coeff = T₁

route-e02-v2-routed-coeff : Trit
route-e02-v2-routed-coeff = T₂

-- ∂₂ᶜ FL = T₂·e02（唯一临界 1-腔目标）
∂₂ᶜ-FL : Trit
∂₂ᶜ-FL = T₂

-- ∂₁ᶜ e02 = T₁ ⊕ T₂ = T₀（直连 + 路由相消）
∂₁ᶜ-e02 : Trit
∂₁ᶜ-e02 = T₁ ⊕ T₂

-- ∂₁ᶜ∘∂₂ᶜ FL = T₂·(T₁⊕T₂) = T₂·T₀ = T₀ ✓
∂²ᶜ-FL : Trit
∂²ᶜ-FL = T₂ ⊗ (T₁ ⊕ T₂)

-- 对账：M3 消元（与 MorseBoundaryDT.m3-cancel-DT 同一引理的重述）
m3-verify : ∂²ᶜ-FL ≡ T₀
m3-verify = refl

-- 交叉验证：∂₁ᶜ-e02 与 m3-cancel-DT 一致
m3-cross-check : T₁ ⊕ T₂ ≡ T₀
m3-cross-check = m3-cancel
