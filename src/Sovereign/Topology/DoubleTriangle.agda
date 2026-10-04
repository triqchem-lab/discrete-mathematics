{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.DoubleTriangle
-- 任务书第五层·5.1 泛型化 M3/M6 测试床：双三角复形（12-1 = 11 胞腔）
--
-- 数学背景：K₃ 上所有合法场的 Morse 复形 ≤1 维（三循环配对被无环性
--   阻断），M3（∂²=0 非平凡消元）需更高维测试床。双三角 = 两三角形
--   共享边 e12：v0..v3（4 顶点）+ e01,e02,e12,e13,e23（5 边）+ FL,FR（2 面）。
--
--   场 V2：v0↦e01, v1↦e12, v3↦e13, e23↦FR；其余临界。
--   临界 = {v2, e02, FL}，m = (1,1,1)——每维恰一临界（完美），
--   且 C₂ᶜ ≠ 0——M3 非平凡消元可行。
--
--   M3 消元预告（oracle 已核，下一模块形式化）：
--     ∂₂ᶜ FL = T₂·e02（直连唯一）
--     ∂₁ᶜ e02 = T₁·v₂（直连）⊕ T₂·v₂（路由 v0↦e01↦v1↦e12→v₂，ε²=T₁）
--     ⟹ T₁ ⊕ T₂ = T₀——路径配对相消 ✓
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.DoubleTriangle where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)

--------------------------------------------------------------------------------
-- §1. 载体：双三角 11 胞腔
--------------------------------------------------------------------------------

data Sx2 : Set where
  v0 v1 v2 v3 : Sx2                     -- 4 顶点
  e01 e02 e12 e13 e23 : Sx2             -- 5 边（e12 = 共享边）
  FL FR : Sx2                           -- 2 面

dim2 : Sx2 → ℕ
dim2 v0 = zero
dim2 v1 = zero
dim2 v2 = zero
dim2 v3 = zero
dim2 e01 = suc zero
dim2 e02 = suc zero
dim2 e12 = suc zero
dim2 e13 = suc zero
dim2 e23 = suc zero
dim2 FL = suc (suc zero)
dim2 FR = suc (suc zero)

--------------------------------------------------------------------------------
-- §2. 离散 Morse 场 V2（4 配对；无环性：修正 Hasse 图无环——构造注记）
--------------------------------------------------------------------------------

V2 : Sx2 → Maybe Sx2
V2 v0 = just e01
V2 v1 = just e12
V2 v2 = nothing
V2 v3 = just e13
V2 e01 = nothing
V2 e02 = nothing
V2 e12 = nothing
V2 e13 = nothing
V2 e23 = just FR
V2 FL = nothing
V2 FR = nothing

--------------------------------------------------------------------------------
-- §3. 临界胞腔见证（3 个：v2 / e02 / FL）
--   IsCritical2 σ := V2 σ ≡ nothing × (∀ τ → V2 τ ≢ just σ)
--------------------------------------------------------------------------------

nothing-just2 : ∀ {τ : Sx2} → ¬ (nothing ≡ just τ)
nothing-just2 ()

IsCritical2 : Sx2 → Set
IsCritical2 σ = (V2 σ ≡ nothing) × (∀ τ → V2 τ ≢ just σ)

-- no-image 证明：11 分支顶层冲突
noImg-v2 : ∀ τ → V2 τ ≢ just v2
noImg-v2 v0 ()
noImg-v2 v1 ()
noImg-v2 v2 h = nothing-just2 h
noImg-v2 v3 ()
noImg-v2 e01 h = nothing-just2 h
noImg-v2 e02 h = nothing-just2 h
noImg-v2 e12 h = nothing-just2 h
noImg-v2 e13 h = nothing-just2 h
noImg-v2 e23 ()
noImg-v2 FL h = nothing-just2 h
noImg-v2 FR h = nothing-just2 h

noImg-e02 : ∀ τ → V2 τ ≢ just e02
noImg-e02 v0 ()
noImg-e02 v1 ()
noImg-e02 v2 h = nothing-just2 h
noImg-e02 v3 ()
noImg-e02 e01 h = nothing-just2 h
noImg-e02 e02 h = nothing-just2 h
noImg-e02 e12 h = nothing-just2 h
noImg-e02 e13 h = nothing-just2 h
noImg-e02 e23 ()
noImg-e02 FL h = nothing-just2 h
noImg-e02 FR h = nothing-just2 h

noImg-FL : ∀ τ → V2 τ ≢ just FL
noImg-FL v0 ()
noImg-FL v1 ()
noImg-FL v2 h = nothing-just2 h
noImg-FL v3 ()
noImg-FL e01 h = nothing-just2 h
noImg-FL e02 h = nothing-just2 h
noImg-FL e12 h = nothing-just2 h
noImg-FL e13 h = nothing-just2 h
noImg-FL e23 ()
noImg-FL FL h = nothing-just2 h
noImg-FL FR h = nothing-just2 h

-- 三个临界见证
crit-v2 : IsCritical2 v2
crit-v2 = refl , noImg-v2

crit-e02 : IsCritical2 e02
crit-e02 = refl , noImg-e02

crit-FL : IsCritical2 FL
crit-FL = refl , noImg-FL

--------------------------------------------------------------------------------
-- §4. m = (1,1,1)：每维恰一临界（完美场——M3 消元的最小非平凡配置）
--------------------------------------------------------------------------------

m-count : dim2 v2 ≡ zero × dim2 e02 ≡ suc zero × dim2 FL ≡ suc (suc zero)
m-count = refl , (refl , refl)

--------------------------------------------------------------------------------
-- §5. 定向系数表（GF(3)；∂e = v_j − v_i 形态；∂FL = e01 + e12 − e02 等）
--
--   M3 消元预告（oracle 已核，下一模块 MorseBoundaryDT 形式化）：
--     ∂₂ᶜ FL = T₂·e02（e02 直连且临界；e01/e12 非临界且 V=nothing 无路由）
--     ∂₁ᶜ e02 = T₁·v₂（直连）⊕ T₂·v₂（路由 e02→v0→e01→v1→e12→v₂，2 箭头 ε²=T₁）
--     直连 T₁ ⊕ 路由 T₂ = T₀ ⟹ ∂₁ᶜ∘∂₂ᶜ = 0 ✓
--------------------------------------------------------------------------------

coeff2E : Sx2 → Sx2 → Trit     -- coeff2E v e = ∂e 的 v 系数
coeff2E v0 e01 = T₂
coeff2E v1 e01 = T₁
coeff2E v0 e02 = T₂
coeff2E v2 e02 = T₁
coeff2E v1 e12 = T₂
coeff2E v2 e12 = T₁
coeff2E v1 e13 = T₂
coeff2E v3 e13 = T₁
coeff2E v2 e23 = T₂
coeff2E v3 e23 = T₁
coeff2E _ _ = T₀

coeff2F : Sx2 → Sx2 → Trit     -- coeff2F e f = ∂f 的 e 系数
coeff2F e01 FL = T₁
coeff2F e02 FL = T₂
coeff2F e12 FL = T₁
coeff2F e12 FR = T₁
coeff2F e13 FR = T₂
coeff2F e23 FR = T₁
coeff2F _ _ = T₀

-- 定向自洽抽查：∂e12 的 v2 系数 T₁（与 K₃ 线 e12 定向一致）
orient-check : coeff2E v2 e12 ≡ T₁
orient-check = refl
