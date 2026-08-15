{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteMaxwellConservation
-- 78 电磁学 — 离散 Maxwell 守恒层: Yee 蛙跳 + 高斯保持 (0 postulate, 无洞)
--
-- 先符号设计, 再落链。闭环的最后一环:
--   静态恒等式 (DiscreteEMCore: div∘curl=0, 规范不变性)
--     → 动态演化 (DiscreteMaxwellTime: 四律谓词 + charge-conservation)
--     → 守恒律 (本模块: Yee 显式更新 + 归纳证明高斯律保持)
--
-- §1 div-time-comm: div ∘ Δt ≡ Δt ∘ div (散度与时间差分交换)
--    直接由 div-linear + div-neg 落链, 呼应"安培两边取散度"的符号推演。
-- §2 Yee 蛙跳显式更新 yee-B / yee-E (构造性动力学, 时间递归定义):
--     B(t+1) = B(t) − curl E(t)
--     E(t+1) = E(t) + curl B(t) − J(t)
--     步进式定义使 FaradayStep / AmpereStep 定义等价成立 (refl)。
-- §3 gauss-preservation: 安培步进 + 连续性 + 初始高斯 ⇒ ∀t 高斯保持
--     对 t 做自然数结构归纳 (Agda 结构递归, 非 postulate), 归纳步
--     用 divE-step (其内核是 div∘curl=0 消去项) + 连续性 + GF(3) 代数。
--
-- 诚实边界: 时间域取 ℕ (守恒定理的归纳需要自然数结构); Fin n 有限时间
-- 窗口可通过对 T ≤ n 的截取获得, 本模块不做 (与用户约定一致, 不写虚假)。
-- 电场的 Yee 更新与磁场的 Yee 更新错半格 (蛙跳), 本模块按标准蛙跳
-- 取 B 序列为原始参数 — 高斯保持定理只依赖 AmpereStep, 与 B 的
-- 更新方式无关, 这正是其代数内涵。

module Sovereign.Physics.DiscreteMaxwellConservation where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

-- 第二基石: GF3 域律 + dx/dy/dz + div/curl + vx/vy/vz
open import Sovereign.Physics.DiscreteEMField3D
-- 核心定理层: addVec3 + div-curl-zero (磁场无源性消去项)
open import Sovereign.Physics.DiscreteEMCore
-- 时间演化层: Time/ΔtV/ΔtS/四律谓词/div-linear/div-neg/divE-step 等
open import Sovereign.Physics.DiscreteMaxwellTime

------------------------------------------------------------------------------
-- §1. div ∘ Δt ≡ Δt ∘ div (散度与时间差分交换, 3 步符号链)
--   div (Δt E) p = div (E(t+1) − E(t)) p
--                = div E(t+1) p + div (−E(t)) p    [div-linear]
--                = div E(t+1) p − div E(t) p       [div-neg]
------------------------------------------------------------------------------

div-time-comm : ∀ E t p →
  div (λ q → ΔtV E t q) p ≡ ΔtS (λ t' q → div (E t') q) t p
div-time-comm E t p = begin
  div (λ q → addVec3 (E (suc t) q) (negVec3 (E t q))) p
    ≡⟨ div-linear (E (suc t)) (λ q → negVec3 (E t q)) p ⟩
  add3 (div (E (suc t)) p) (div (λ q → negVec3 (E t q)) p)
    ≡⟨ cong (add3 (div (E (suc t)) p)) (div-neg (E t) p) ⟩
  add3 (div (E (suc t)) p) (neg3 (div (E t) p)) ∎

------------------------------------------------------------------------------
-- §2. Yee 蛙跳显式更新 (构造性动力学, 时间结构递归)
--   步进式定义 ⟹ FaradayStep / AmpereStep 定义等价成立 (refl)。
------------------------------------------------------------------------------

yee-B : VecFieldTime → VecFieldTime → VecFieldTime
yee-B B E zero = B zero
yee-B B E (suc t) = λ q → addVec3 (yee-B B E t q) (negVec3 (curl (E t) q))

yee-E : VecFieldTime → VecFieldTime → VecFieldTime → VecFieldTime
yee-E E B J zero = E zero
yee-E E B J (suc t) = λ q → addVec3 (yee-E E B J t q) (addVec3 (curl (B t) q) (negVec3 (J t q)))

yee-faraday-step : ∀ B E → FaradayStep (yee-B B E) E
yee-faraday-step B E t = refl

yee-ampere-step : ∀ E B J → AmpereStep (yee-E E B J) B J
yee-ampere-step E B J t = refl

------------------------------------------------------------------------------
-- §3. 高斯保持定理 (ℕ 结构归纳, 非 postulate)
--   安培步进 + 连续性 (Δt ρ = −div J) + 初始高斯
--   ⇒ 对所有 t 高斯律保持: div E(t) = ρ(t)。
--   归纳步:
--     div E(t+1) = div E(t) − div J(t)      [divE-step, 内核 div∘curl=0]
--               = ρ(t) + (ρ(t+1) − ρ(t))    [归纳假设 + 连续性]
--               = ρ(t+1)                     [GF(3) 交换/结合/逆元]
------------------------------------------------------------------------------

gauss-preservation : (E B J : VecFieldTime) (ρ : ScalFieldTime)
  → AmpereStep E B J
  → (∀ t p → ΔtS ρ t p ≡ neg3 (div (J t) p))
  → (∀ p → div (E zero) p ≡ ρ zero p)
  → GaussHolds E ρ
gauss-preservation E B J ρ Estep cont base = go
  where
  go : ∀ t p → div (E t) p ≡ ρ t p
  go zero p = base p
  go (suc t) p = begin
    div (E (suc t)) p
      ≡⟨ divE-step E B J Estep t p ⟩
    add3 (div (E t) p) (neg3 (div (J t) p))
      ≡⟨ cong (λ x → add3 x (neg3 (div (J t) p))) (go t p) ⟩
    add3 (ρ t p) (neg3 (div (J t) p))
      ≡⟨ cong (add3 (ρ t p)) (sym (cont t p)) ⟩
    add3 (ρ t p) (add3 (ρ (suc t) p) (neg3 (ρ t p)))
      ≡⟨ sym (add3-assoc (ρ t p) (ρ (suc t) p) (neg3 (ρ t p))) ⟩
    add3 (add3 (ρ t p) (ρ (suc t) p)) (neg3 (ρ t p))
      ≡⟨ cong (λ x → add3 x (neg3 (ρ t p))) (add3-comm (ρ t p) (ρ (suc t) p)) ⟩
    add3 (add3 (ρ (suc t) p) (ρ t p)) (neg3 (ρ t p))
      ≡⟨ add3-assoc (ρ (suc t) p) (ρ t p) (neg3 (ρ t p)) ⟩
    add3 (ρ (suc t) p) (add3 (ρ t p) (neg3 (ρ t p)))
      ≡⟨ cong (add3 (ρ (suc t) p)) (add3-inverse (ρ t p)) ⟩
    add3 (ρ (suc t) p) fz
      ≡⟨ add3-identity (ρ (suc t) p) ⟩
    ρ (suc t) p ∎

-- Yee 组合: 显式更新场的高斯保持 (初始 E 高斯 + 连续性 ⇒ 所有步高斯)
yee-gauss-preservation :
  (E B J : VecFieldTime) (ρ : ScalFieldTime)
  → (∀ t p → ΔtS ρ t p ≡ neg3 (div (J t) p))
  → (∀ p → div (E zero) p ≡ ρ zero p)
  → ∀ t p → div (yee-E E B J t) p ≡ ρ t p
yee-gauss-preservation E B J ρ cont base t p =
  gauss-preservation (yee-E E B J) B J ρ (yee-ampere-step E B J) cont base t p

-- 0 postulate.
