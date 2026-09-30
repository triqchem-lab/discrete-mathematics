{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Zomega
-- Z[ω] 环律提升层: 把 RootMath.Eisenstein 已证环律迁移到 A4Representation 的 Zω 载体
--
-- 数学背景:
--   Z[ω] = Eisenstein 整数环 ℤ[ω], ω² + ω + 1 = 0 (即 ω² = -1-ω, ω³ = 1)。
--   元素 a + bω (a,b ∈ ℤ), 乘法 (a+bω)(c+dω) = (ac-bd) + (ad+bc-bd)ω
--   — ω² = -1-ω 是化简关键 (bd·ω² = -bd - bd·ω, 并入常数项与 ω 项)。
--
-- 载体勘定 (勿重定义):
--   Zω / mkZω / addZω / mulZω / negZω / zeroZω / oneZω 已在
--   Sovereign.Structology.A4Representation 定义 (记录对 (a,b) ∈ ℤ²)。
--   本模块 import 复用, 只补环律, 不新增载体。
--
-- 路径选型 (A: 逐分量代数链 —— 已在库内完成, 本模块做迁移而不重证):
--   Sovereign.RootMath.Eisenstein 的 Eisenstein 载体与 Zω 的运算公式逐字同形
--   (同一 ℤ 运算、同一 ω²=-1-ω 化简形), 且已证全套环律:
--     +ᵉ-comm / +ᵉ-assoc / +ᵉ-identityˡʳ / +ᵉ-inverseˡʳ
--     *ᵉ-comm / *ᵉ-assoc / *ᵉ-identityˡʳ / *ᵉ-distribˡʳ
--   本模块经「记录分量投影桥」liftEis (§0) 把定理迁到 Zω —— 不重复 ≈250 行
--   分量代数链 (重新证明已有引理 = 浪费)。零元律 Eisenstein 未收, 由 §3 直接补。
--   对抗验证 §4 给出具体点 refl 交叉比对 (直接计算 vs 定理实例)。
--
-- 用途: A4ThreeDimRep 的 rho3-hom 生成元路线 —— mulMat 结合/分配律展开的
--   Zω 分量证明消耗 mulZω-assoc / mulZω-distribˡʳ / mulZω-comm (dot 重排)。
--
-- 0 postulate / 0 hole / 0 sorry。

module Sovereign.Algebra.Zomega where

open import Data.Integer.Base using (ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Integer.Properties using (*-zeroˡ; *-zeroʳ; neg-involutive)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Structology.A4Representation
  using (Zω; mkZω; addZω; negZω; mulZω; zeroZω; oneZω; ω; ω²)
open import Sovereign.RootMath.Eisenstein
  using (Eisenstein; eis; _+ᵉ_; _*ᵉ_;
         +ᵉ-comm; +ᵉ-assoc; +ᵉ-identityˡ; +ᵉ-identityʳ; +ᵉ-inverseˡ; +ᵉ-inverseʳ;
         *ᵉ-comm; *ᵉ-assoc; *ᵉ-identityˡ; *ᵉ-identityʳ; *ᵉ-distribˡ; *ᵉ-distribʳ)

--------------------------------------------------------------------------------
-- §0. 记录分量投影桥: Eisenstein 等式 → Zω 等式
--   两载体是同一乘法公式的两次定义 (mkZω (a*c-b*d) (a*d+b*c-b*d) ↔ eis 同形),
--   故 Eisenstein 定理的两个分量投影就是 Zω 目标的两个分量。
--------------------------------------------------------------------------------

eisA : Eisenstein → ℤ
eisA (eis x _) = x

eisB : Eisenstein → ℤ
eisB (eis _ y) = y

-- 桥: Eisenstein 上的等式 ⇒ Zω 上的等式 (两侧分量定义同形, 直接对齐)
liftEis : ∀ {x y : Eisenstein} → x ≡ y → mkZω (eisA x) (eisB x) ≡ mkZω (eisA y) (eisB y)
liftEis p = cong₂ mkZω (cong eisA p) (cong eisB p)

--------------------------------------------------------------------------------
-- §1. 加法: 交换幺半群 + 逆 (addZω / negZω / zeroZω)
--------------------------------------------------------------------------------

addZω-comm : ∀ x y → addZω x y ≡ addZω y x
addZω-comm (mkZω a b) (mkZω c d) = liftEis (+ᵉ-comm (eis a b) (eis c d))

addZω-assoc : ∀ x y z → addZω (addZω x y) z ≡ addZω x (addZω y z)
addZω-assoc (mkZω a b) (mkZω c d) (mkZω e f) = liftEis (+ᵉ-assoc (eis a b) (eis c d) (eis e f))

addZω-identityˡ : ∀ x → addZω zeroZω x ≡ x
addZω-identityˡ (mkZω a b) = liftEis (+ᵉ-identityˡ (eis a b))

addZω-identityʳ : ∀ x → addZω x zeroZω ≡ x
addZω-identityʳ (mkZω a b) = liftEis (+ᵉ-identityʳ (eis a b))

addZω-inverseˡ : ∀ x → addZω (negZω x) x ≡ zeroZω
addZω-inverseˡ (mkZω a b) = liftEis (+ᵉ-inverseˡ (eis a b))

addZω-inverseʳ : ∀ x → addZω x (negZω x) ≡ zeroZω
addZω-inverseʳ (mkZω a b) = liftEis (+ᵉ-inverseʳ (eis a b))

negZω-involutive : ∀ x → negZω (negZω x) ≡ x
negZω-involutive (mkZω a b) = cong₂ mkZω (neg-involutive a) (neg-involutive b)

--------------------------------------------------------------------------------
-- §2. 乘法: 交换幺半群 (mulZω / oneZω) —— 核心: 结合律
--------------------------------------------------------------------------------

mulZω-assoc : ∀ x y z → mulZω (mulZω x y) z ≡ mulZω x (mulZω y z)
mulZω-assoc (mkZω a b) (mkZω c d) (mkZω e f) = liftEis (*ᵉ-assoc (eis a b) (eis c d) (eis e f))

mulZω-comm : ∀ x y → mulZω x y ≡ mulZω y x
mulZω-comm (mkZω a b) (mkZω c d) = liftEis (*ᵉ-comm (eis a b) (eis c d))

mulZω-identityˡ : ∀ x → mulZω oneZω x ≡ x
mulZω-identityˡ (mkZω a b) = liftEis (*ᵉ-identityˡ (eis a b))

mulZω-identityʳ : ∀ x → mulZω x oneZω ≡ x
mulZω-identityʳ (mkZω a b) = liftEis (*ᵉ-identityʳ (eis a b))

--------------------------------------------------------------------------------
-- §3. 分配律与零元 (mulZω / addZω 交互)
--------------------------------------------------------------------------------

mulZω-distribˡ : ∀ x y z → mulZω x (addZω y z) ≡ addZω (mulZω x y) (mulZω x z)
mulZω-distribˡ (mkZω a b) (mkZω c d) (mkZω e f) =
  liftEis (*ᵉ-distribˡ (eis a b) (eis c d) (eis e f))

mulZω-distribʳ : ∀ x y z → mulZω (addZω x y) z ≡ addZω (mulZω x z) (mulZω y z)
mulZω-distribʳ (mkZω a b) (mkZω c d) (mkZω e f) =
  liftEis (*ᵉ-distribʳ (eis a b) (eis c d) (eis e f))

-- 零元律 (Eisenstein 未收, 由 ℤ 的 *-zeroˡ/ʳ 直接补)
mulZω-zeroˡ : ∀ x → mulZω zeroZω x ≡ zeroZω
mulZω-zeroˡ (mkZω a b) = cong₂ mkZω comp1 comp2
  where
  comp1 : + 0 * a - + 0 * b ≡ + 0
  comp1 = trans (cong₂ _-_ (*-zeroˡ a) (*-zeroˡ b)) refl

  comp2 : + 0 * b + + 0 * a - + 0 * b ≡ + 0
  comp2 = trans (cong₂ (λ u v → u + v - u) (*-zeroˡ b) (*-zeroˡ a)) refl

mulZω-zeroʳ : ∀ x → mulZω x zeroZω ≡ zeroZω
mulZω-zeroʳ (mkZω a b) = cong₂ mkZω comp1 comp2
  where
  comp1 : a * + 0 - b * + 0 ≡ + 0
  comp1 = trans (cong₂ _-_ (*-zeroʳ a) (*-zeroʳ b)) refl

  comp2 : a * + 0 + b * + 0 - b * + 0 ≡ + 0
  comp2 = trans (cong₂ (λ u v → u + v - v) (*-zeroʳ a) (*-zeroʳ b)) refl

--------------------------------------------------------------------------------
-- §4. 对抗验证: 具体点上「直接计算」与「定理实例」交叉比对
--   全部具体 ℤ 常数: refl 闭合 = 定义归约到同一闭项;
--   同一等式再由 §1–§3 定理实例给出第二路径, 两路一致才闭合。
--------------------------------------------------------------------------------

private
  x₁ y₁ z₁ : Zω
  x₁ = mkZω (+ 2) -[1+ 0 ]      -- 2 - ω
  y₁ = mkZω -[1+ 1 ] (+ 3)      -- -2 + 3ω
  z₁ = ω                        -- ω

-- 结合律: 路径 1 = 直接计算
assoc-check-calc : mulZω (mulZω x₁ y₁) z₁ ≡ mulZω x₁ (mulZω y₁ z₁)
assoc-check-calc = refl

-- 结合律: 路径 2 = 定理实例
assoc-check-thm : mulZω (mulZω x₁ y₁) z₁ ≡ mulZω x₁ (mulZω y₁ z₁)
assoc-check-thm = mulZω-assoc x₁ y₁ z₁

-- 分配律: 路径 1 = 直接计算
distrib-check-calc : mulZω x₁ (addZω y₁ z₁) ≡ addZω (mulZω x₁ y₁) (mulZω x₁ z₁)
distrib-check-calc = refl

-- 分配律: 路径 2 = 定理实例
distrib-check-thm : mulZω x₁ (addZω y₁ z₁) ≡ addZω (mulZω x₁ y₁) (mulZω x₁ z₁)
distrib-check-thm = mulZω-distribˡ x₁ y₁ z₁

-- 交换律: 直接计算
comm-check-calc : mulZω x₁ y₁ ≡ mulZω y₁ x₁
comm-check-calc = refl

-- ω 关系式 sanity: ω³ = 1 在 mulZω 下闭合 (与 A4Representation.omega-cubed 同源)
omega-cubed-check : mulZω (mulZω ω ω) ω ≡ oneZω
omega-cubed-check = refl

-- ω² = -1 - ω 在 mulZω 下闭合 (与 A4Representation.omega-squared-form 同源)
omega-squared-check : mulZω ω ω ≡ addZω (negZω oneZω) (negZω ω)
omega-squared-check = refl

-- 0 postulate.
