{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.NoetherTheorem
-- Noether 定理统一结构 (L3 深层证明)
--
-- 核心命题:
--   将离散 Noether 定理、规范对称性、电荷守恒统一为一个自洽的框架。
--
-- 证明策略:
--   §1 规范对称性 (⟨α⟩ 规范群)
--   §2 Noether 恒等式 (变分导数与守恒流)
--   §3 电荷守恒 (div J + Δt ρ = 0)
--   §4 守恒律总结
--
-- 全部 0 postulate, GF(3) 穷举 refl + 符号推理。
--
-- 【诚实边界】离散基座实例核——连续 Noether 全定理（变分导数↔守恒流）不在本框架；
-- §1-§4 为既有件引用清单（证据在 Physics/ 各模块），§5 为本模块实证层（自有证明体）。

-- | Noether 定理离散实例核
--
-- 核心原则：Noether 定理离散实例核——离散基座实例核（非一般定理，诚实边界随引用）
--          穷举/归纳边界遵守（≤27 case 或具名链，trans ≤3）
--          代数污染禁令（禁 Float/Double/超越函数）
--
-- 包含：§5 离散 Noether 原理（iterate/IsSymmetry/Conserved/noether-core）
--       + GF(3) 双实例（ℤ/2 交换对称⟹⊕-和守恒；ℤ/3 旋转对称⟹⊕-和守恒）
--       + 核对件（具体点 refl 交叉）

module Sovereign.Analysis.NoetherTheorem where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; ⊕-comm; ⊕-assoc)
open import Sovereign.Physics.DiscreteEMField3D
  using (Point3D; GF3; ScalarField; VectorField; next;
         dx; dy; dz; grad; curl; div; vx; vy; vz;
         add3; neg3; add3-comm; add3-assoc; add3-identity; add3-inverse;
         neg3-involutive; neg3-add)
open import Sovereign.Physics.DiscreteActionPrinciple
  using (GaugeGroup; e; gα; gα²; gα³; _*g_; g-inv; embedG;
         g-assoc; g-identityˡ; g-identityʳ; g-inverseˡ; g-inverseʳ;
         embedG-hom; g-norm-is-1)
open import Sovereign.Physics.DiscreteNoether
  using (neg-add-identity; add-neg-zero; neg-add-distrib;
         noether-1d-point0; noether-1d-point1; noether-1d-point2;
         diff-comm)
open import Sovereign.Physics.DiscreteMaxwellTime
  using (charge-conservation; FaradayHolds; AmpereHolds; GaussHolds)

open ≡-Reasoning

--------------------------------------------------------------------------------
-- §1. 规范对称性
--------------------------------------------------------------------------------

-- 规范群: ⟨α⟩ = {1, α, α², α³} ⊂ GF(9)*
-- 已有: GaugeGroup = {e, gα, gα², gα³}

-- 规范群公理 (L2 全称)
-- 已有: g-assoc, g-identityˡ, g-identityʳ, g-inverseˡ, g-inverseʳ

-- 规范群嵌入 GF(9) (L2 全称)
-- 已有: embedG-hom : ∀ p q → embedG(p*q) = embedG(p)*embedG(q)

-- 规范群范数恒为 1 (L2 全称)
-- 已有: g-norm-is-1 : ∀ p → galoisNorm(embedG p) ≡ T₁

--------------------------------------------------------------------------------
-- §2. Noether 恒等式
--------------------------------------------------------------------------------

-- Noether 恒等式: 变分导数与守恒流的关系
-- δS/δφ = 0 → ∂L/∂(∂φ) · δφ = 守恒流

-- 差分算子交换: ∇(Δtχ) = Δt∇χ
-- 已有: diff-comm : ∀ a b c d → diff-op (Δt χ) ≡ Δt (diff-op χ)

-- Noether 恒等式 (1D, 3 点)
-- 已有: noether-1d-point0/1/2 : ∀ Jx → ...

--------------------------------------------------------------------------------
-- §3. 电荷守恒
--------------------------------------------------------------------------------

-- 电荷守恒: Δt ρ = -div J
-- 从 Ampère 定律 + Gauss 定律推导
-- 已有: charge-conservation : ∀ E B J ρ → AmpereStep E B J → GaussHolds E ρ → ...

-- 电荷守恒定理 (L3 深层)
-- 证明链:
-- 1. Ampère: Δt E = curl B - J
-- 2. Gauss: div E = ρ
-- 3. div(Δt E) = div(curl B - J) = -div J (因为 div(curl B)=0)
-- 4. Δt(div E) = -div J
-- 5. Δt ρ = -div J (由 Gauss 定律)

--------------------------------------------------------------------------------
-- §4. 守恒律总结
--------------------------------------------------------------------------------

-- Noether 定理总结:
-- 1. 连续对称性 → 守恒律
-- 2. 规范对称性 → 电荷守恒
-- 3. 时间平移对称性 → 能量守恒
-- 4. 空间平移对称性 → 动量守恒

-- 在离散格点上:
-- 1. ⟨α⟩ 规范对称性 → 电荷守恒 (已有 charge-conservation)
-- 2. 时间步进对称性 → 能量守恒 (待实现)
-- 3. 空间平移对称性 → 动量守恒 (待实现)

-- 0 postulate.

--------------------------------------------------------------------------------
-- §5. 离散 Noether 原理（本模块实证层——对称 ⟹ 守恒的构造性核）
--------------------------------------------------------------------------------
-- 数学：观测量 q 沿变换 f 的轨道守恒 ⇐ f 保 q（IsSymmetry）。
--   这是 Noether「对称性⟨守恒量」的离散/组合版：不变量沿对称轨道逐点恒定，
--   证明 = 对迭代步数归纳 + 2 步链（对称步 → 归纳步）。
-- T⁶/GF(3) 对接：相位对称（ℤ/2 交换 / C₃ 旋转）⟹ 幅度和（⊕-和）守恒——
--   「相位动、幅度不动」正是相位不可约性元公理的守恒面。

-- 迭代（轨道步进）
iterate : ∀ {A : Set} → ℕ → (A → A) → A → A
iterate zero f x = x
iterate (suc n) f x = f (iterate n f x)

-- 对称 = 保观测量的变换（定义层——关系即定义，零公理）
IsSymmetry : ∀ {A B : Set} → (q : A → B) → (f : A → A) → Set
IsSymmetry q f = ∀ x → q (f x) ≡ q x

-- 守恒 = 观测量沿轨道恒定
Conserved : ∀ {A B : Set} → (q : A → B) → (f : A → A) → Set
Conserved q f = ∀ n x → q (iterate n f x) ≡ q x

-- 核心定理（离散 Noether）：对称 ⟹ 守恒
-- 策略：对 n 归纳；suc 案 2 步链 [对称步 f-sym → 归纳步 IH]
noether-core : ∀ {A B : Set} (q : A → B) (f : A → A) → IsSymmetry q f → Conserved q f
noether-core q f f-sym zero x = refl
noether-core q f f-sym (suc n) x =
  trans (f-sym (iterate n f x)) (noether-core q f f-sym n x)

--------------------------------------------------------------------------------
-- §5.1 GF(3) 实例一：ℤ/2 交换对称 ⟹ ⊕-和守恒
--------------------------------------------------------------------------------

swap2 : Trit × Trit → Trit × Trit
swap2 (a , b) = (b , a)

q⊕2 : Trit × Trit → Trit
q⊕2 (a , b) = a ⊕ b

-- 对称步：⊕-交换（复用 Trit.⊕-comm——零重证）
swap2-sym : IsSymmetry q⊕2 swap2
swap2-sym (a , b) = ⊕-comm b a

noether-swap2 : ∀ n p → q⊕2 (iterate n swap2 p) ≡ q⊕2 p
noether-swap2 = noether-core q⊕2 swap2 swap2-sym

--------------------------------------------------------------------------------
-- §5.2 GF(3) 实例二：ℤ/3 旋转对称 ⟹ ⊕-和守恒（C₃ 相位旋转不动幅度和）
--------------------------------------------------------------------------------

rot3 : Trit × Trit × Trit → Trit × Trit × Trit
rot3 (a , b , c) = (b , c , a)

q⊕3 : Trit × Trit × Trit → Trit
q⊕3 (a , b , c) = (a ⊕ b) ⊕ c

-- 对称步：2 步链 [⊕-comm (b⊕c) a → sym ⊕-assoc]（复用 Trit 件——零重证）
rot3-sym : IsSymmetry q⊕3 rot3
rot3-sym (a , b , c) = trans (⊕-comm (b ⊕ c) a) (sym (⊕-assoc a b c))

noether-rot3 : ∀ n p → q⊕3 (iterate n rot3 p) ≡ q⊕3 p
noether-rot3 = noether-core q⊕3 rot3 rot3-sym

--------------------------------------------------------------------------------
-- §5.3 核对层（具体点 refl 交叉）
--------------------------------------------------------------------------------

-- ℤ/2 轨道三步回 (T₀,T₁)→(T₁,T₀)→(T₀,T₁)→(T₁,T₀)：⊕-和恒为 T₁
check-noether-1 : q⊕2 (iterate 3 swap2 (T₀ , T₁)) ≡ T₁
check-noether-1 = refl

-- C₃ 轨道两步 (T₀,T₁,T₂)→(T₁,T₂,T₀)→(T₂,T₀,T₁)：⊕-和恒为 T₀
check-noether-2 : q⊕3 (iterate 2 rot3 (T₀ , T₁ , T₂)) ≡ T₀
check-noether-2 = refl

-- 轨道闭合核对：swap2⁴ = id（ℤ/2 阶 2 的平方轨道自合）
check-noether-3 : ∀ p → iterate 2 swap2 p ≡ p
check-noether-3 (a , b) = refl
