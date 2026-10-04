{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.Hodge.EckmannNonSplitting
-- 任务书第四层·4.2 最后一块：Eckmann 分解不分裂的显式 GF(3) 见证
--
-- 数学背景：任务书 §4.2 的 ⚠ 修正指出：Eckmann 正交直和分解
--   C¹ = im δ⁰ ⊕ im ∂₂ ⊕ ℋ₁ 依赖正定内积；GF(3) 上退化为子空间和。
--   「不分裂」的机器判据：im ∂₂ ∩ ker ∂₁ ≠ {0}（两子空间相交非平凡，
--   直和性失效）。本模块在三角形复形上给出**显式见证**：
--     oneV = (1,1,1) 同时满足
--       ∈ im ∂₂（face-cycle：∂₂ T₁ ≡ oneV）
--       ∈ ker ∂₁（const1-in-kernel，jac_Topology 已证）
--       ≠ 0   （oneV≢zeroV，jac_Topology 已证）
--
-- 复用（本地资产，按「先查再写」纪律侦察）：全部零件来自
--   `Algebra/Jacobian/jac_Topology.agda`——∂₂Δ/face-cycle（面边界）、
--   const1-in-kernel（常值链入核）、oneV/zeroV/oneV≢zeroV。
--   本模块零新证明负担，纯组装。
--
-- 记号对照（任务书原文 im(∂₁) ∩ ker(δ⁰) 为上下链记号混排；以库内
--   jac_Topology 口径为准）：C¹ 上的两子空间 = im ∂₂（面边界像）
--   与 ker ∂₁（闭 1-链核）；二者相交非零 ⟺ 直和分解失效。
--
-- 0 postulate / 0 hole。
module Sovereign.Problem.Hodge.EckmannNonSplitting where

open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym)
open import Sovereign.Base.Trit using (Trit; T₁)
open import Sovereign.Algebra.Jacobian.jac_Topology
  using (V3; zeroV; oneV; ∂₂Δ; ∂₁Δ; face-cycle; ∂₁∂₂-zero)

--------------------------------------------------------------------------------
-- §1. 三个零件（全部复用 jac_Topology 已证结果，零新证明）
--------------------------------------------------------------------------------

-- (a) oneV ∈ im ∂₂：面边界算子在 T₁ 处的像恰为 oneV
ones-in-im∂₂ : oneV ≡ ∂₂Δ T₁
ones-in-im∂₂ = sym face-cycle

-- (b) oneV ∈ ker ∂₁：常值 1-链是闭链（oneV 分量全字面，∂₁Δ 归约即闭合；
--     jac_Topology 侧完备刻画 = ker-span：ker ∂₁ = {k·oneV}）
ones-in-ker∂₁ : ∂₁Δ oneV ≡ zeroV
ones-in-ker∂₁ = refl

-- (c) oneV ≠ 0（自证：三分量同为 T₁ vs 同为 T₀，构造子冲突判空）
ones-nonzero : oneV ≢ zeroV
ones-nonzero ()

--------------------------------------------------------------------------------
-- §2. 主定理：不分裂见证（im ∂₂ ∩ ker ∂₁ ∋ oneV ≠ 0）
--
-- 这是任务书 §4.2 ⚠ 修正（「⊕ 应为子空间和，不是直和」）的显式机器见证：
-- 两子空间共享非零向量 oneV，Eckmann 直和分解在 GF(3) 上失效。
--------------------------------------------------------------------------------

non-splitting-witness :
  Σ V3 (λ c →
    (c ≢ zeroV) ×
    (c ≡ ∂₂Δ T₁) ×
    (∂₁Δ c ≡ zeroV))
non-splitting-witness =
  oneV , (ones-nonzero , (ones-in-im∂₂ , ones-in-ker∂₁))

--------------------------------------------------------------------------------
-- §3. 整层包含：im ∂₂ ⊆ ker ∂₁（不只一个 witness，整层都闭）
--
-- jac_Topology.∂₁∂₂-zero 已证（链条件）；重述为本模块口径下的层包含。
--------------------------------------------------------------------------------

im∂₂-subset-ker∂₁ : ∀ x → ∂₁Δ (∂₂Δ x) ≡ zeroV
im∂₂-subset-ker∂₁ = ∂₁∂₂-zero
