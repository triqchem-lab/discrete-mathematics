{-# OPTIONS --rewriting #-}
module Sovereign.PDE.WaveEquationDiscrete where

--------------------------------------------------------------------------------
-- GF(3) 离散波动方程 — MSC 35L05 (波动方程) 的离散本源
--
-- 连续波动方程: u_{tt} = c²·u_{xx} (能量守恒, 时间可逆)
-- GF(3) 波动方程: u_{n+1} = 2u_n - u_{n-1} + r²·Δ_L u_n
--
-- 在 GF(3) 中:
--   2 = T₂, -1 = T₂ (因为 -1 ≡ 2 mod 3)
--   r² = T₁ (GF(3) 中唯一的非零平方值)
--   Δ_L u = (sum3 u, sum3 u, sum3 u) (见 HeatEquationDiscrete)
--
-- 核心发现:
--   1. 常数稳态: waveStep(const c, const c) = (const c, const c)
--   2. 可逆性: 波动步进是有限状态空间上的置换 (729 个状态)
--   3. 能量: 定义动能+势能, 常数态能量为 T₀
--   4. 连续能量守恒是 GF(3) 有限置换的"不存在的极限"投影
--
-- 依赖:
--   Trit: GF(3) 代数
--   ProjectionDifferential: Δ, sum3, GF3Func
--   DiscreteDE: triple-≡
--
-- 0 postulate — 全部构造性证明 (穷举法)
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (
  _≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.ProjectionDifferential using (
  GF3Func; Δ; sum3; const-func; Δ-const-zero)
open import Sovereign.Algebra.DiscreteDE using (
  triple-≡)

--------------------------------------------------------------------------------
-- §1. 波动方程状态空间与步进
--
-- 连续: u_{tt} = c²·Δu, 状态 = (u, u_t) (位移 + 速度)
-- GF(3): u_{n+1} = T₂⊗u_n ⊕ negate(u_{n-1}) ⊕ (s,s,s)
--   状态 = (u_n, u_{n-1}) (当前 + 前一步)
--   s = sum3(u_n) (离散 Laplace 值)
--
-- 在 GF(3) 中:
--   2u_n = T₂⊗u_n
--   -u_{n-1} = negate(u_{n-1}) = T₂⊗u_{n-1}
--   r² = T₁ (CFL 数 r = 1, r² = 1)
--------------------------------------------------------------------------------

-- 波动方程状态: (u_n, u_{n-1})
WaveState : Set
WaveState = GF3Func × GF3Func

-- GF(3) 平方函数
sq : Trit → Trit
sq x = x ⊗ x

-- 波动方程步进
-- u_{n+1}(i) = T₂⊗u_n(i) ⊕ negate(u_{n-1}(i)) ⊕ sum3(u_n)
waveStep : WaveState → WaveState
waveStep ((u₀ , u₁ , u₂) , (v₀ , v₁ , v₂)) =
  ((u₀' , u₁' , u₂') , (u₀ , u₁ , u₂))
  where
    s  = (u₀ ⊕ u₁) ⊕ u₂
    u₀' = ((T₂ ⊗ u₀) ⊕ (negate v₀)) ⊕ s
    u₁' = ((T₂ ⊗ u₁) ⊕ (negate v₁)) ⊕ s
    u₂' = ((T₂ ⊗ u₂) ⊕ (negate v₂)) ⊕ s

--------------------------------------------------------------------------------
-- §2. 动能 + 势能 = 总能量
--
-- 连续: E = ½∫u_t² dx + ½c²∫|∇u|² dx
-- GF(3):
--   动能 K(u,v) = Σ (u_i ⊖ v_i)² (速度平方和)
--   势能 V(u) = Σ (Δu_i)² (梯度平方和)
--   总能量 E = K ⊕ V
--
-- 注: GF(3) 中 ½ = 2⁻¹ = T₂, 但此处省略系数 (不影响守恒性验证)
--------------------------------------------------------------------------------

-- 动能: K(u,v) = Σ (u_i ⊕ negate(v_i))²
kineticEnergy : WaveState → Trit
kineticEnergy ((u₀ , u₁ , u₂) , (v₀ , v₁ , v₂)) =
  (sq (u₀ ⊕ negate v₀) ⊕ sq (u₁ ⊕ negate v₁)) ⊕ sq (u₂ ⊕ negate v₂)

-- 势能: V(u) = Σ (Δu_i)²
potentialEnergy : GF3Func → Trit
potentialEnergy (u₀ , u₁ , u₂) =
  (sq (u₁ ⊕ negate u₀) ⊕ sq (u₂ ⊕ negate u₁)) ⊕ sq (u₀ ⊕ negate u₂)

-- 总能量: E = K ⊕ V
totalEnergy : WaveState → Trit
totalEnergy (u , v) = kineticEnergy (u , v) ⊕ potentialEnergy u

--------------------------------------------------------------------------------
-- §3. 常数稳态
--
-- 连续: u ≡ c 是波动方程的平凡解
-- GF(3): waveStep(const c, const c) = (const c, const c)
--
-- 证明: T₂⊗c ⊕ negate(c) ⊕ sum3(const c)
--       = T₂⊗c ⊕ T₂⊗c ⊕ T₀  (negate = T₂⊗_, sum3 = 3c = 0)
--       = (T₂⊕T₂)⊗c = T₁⊗c = c
--------------------------------------------------------------------------------

-- T₂⊗c ⊕ negate(c) = c (GF(3) 中 -2c = c, 即 T₂c + T₂c = c)
wave-const-component : ∀ c → (T₂ ⊗ c) ⊕ (negate c) ≡ c
wave-const-component T₀ = refl
wave-const-component T₁ = refl
wave-const-component T₂ = refl

-- 常数稳态: waveStep(const c, const c) = (const c, const c)
wave-const-steady : ∀ c →
  waveStep (const-func c , const-func c) ≡ (const-func c , const-func c)
wave-const-steady T₀ = refl
wave-const-steady T₁ = refl
wave-const-steady T₂ = refl

--------------------------------------------------------------------------------
-- §4. 可逆性 — 波动步进是有限状态置换
--
-- 连续波动方程: 时间可逆 (u_{-1} = 2u_0 - u_1 + Δu_0)
-- GF(3): 波动步进是 GF3Func² (729 元素) 上的双射
--
-- 逆步进: 从 (u_{n+1}, u_n) 恢复 u_{n-1}
--   u_{n-1}(i) = T₂⊗u_{n+1}(i) ⊕ T₂⊗u_n(i) ⊕ sum3(u_n)
--
-- 代数验证:
--   T₂⊗(T₂⊗a ⊕ negate(b) ⊕ c) ⊕ T₂⊗a ⊕ c
--   = T₁⊗a ⊕ T₂⊗negate(b) ⊕ T₂⊗c ⊕ T₂⊗a ⊕ c
--   = a ⊕ T₁⊗b ⊕ T₂⊗c ⊕ T₂⊗a ⊕ c  (T₂⊗negate(b) = T₂⊗T₂⊗b = b)
--   = (T₁⊕T₂)⊗a ⊕ b ⊕ (T₂⊕T₁)⊗c
--   = T₀⊗a ⊕ b ⊕ T₀⊗c = b  ∎
--------------------------------------------------------------------------------

-- 分量级逆引理 (27 case 穷举)
wave-inverse-component : ∀ a b c →
  ((T₂ ⊗ (((T₂ ⊗ a) ⊕ (negate b)) ⊕ c)) ⊕ (T₂ ⊗ a)) ⊕ c ≡ b
wave-inverse-component T₀ T₀ T₀ = refl
wave-inverse-component T₀ T₀ T₁ = refl
wave-inverse-component T₀ T₀ T₂ = refl
wave-inverse-component T₀ T₁ T₀ = refl
wave-inverse-component T₀ T₁ T₁ = refl
wave-inverse-component T₀ T₁ T₂ = refl
wave-inverse-component T₀ T₂ T₀ = refl
wave-inverse-component T₀ T₂ T₁ = refl
wave-inverse-component T₀ T₂ T₂ = refl
wave-inverse-component T₁ T₀ T₀ = refl
wave-inverse-component T₁ T₀ T₁ = refl
wave-inverse-component T₁ T₀ T₂ = refl
wave-inverse-component T₁ T₁ T₀ = refl
wave-inverse-component T₁ T₁ T₁ = refl
wave-inverse-component T₁ T₁ T₂ = refl
wave-inverse-component T₁ T₂ T₀ = refl
wave-inverse-component T₁ T₂ T₁ = refl
wave-inverse-component T₁ T₂ T₂ = refl
wave-inverse-component T₂ T₀ T₀ = refl
wave-inverse-component T₂ T₀ T₁ = refl
wave-inverse-component T₂ T₀ T₂ = refl
wave-inverse-component T₂ T₁ T₀ = refl
wave-inverse-component T₂ T₁ T₁ = refl
wave-inverse-component T₂ T₁ T₂ = refl
wave-inverse-component T₂ T₂ T₀ = refl
wave-inverse-component T₂ T₂ T₁ = refl
wave-inverse-component T₂ T₂ T₂ = refl

-- 逆步进定义
waveStepInverse : WaveState → WaveState
waveStepInverse ((u₀ , u₁ , u₂) , (w₀ , w₁ , w₂)) =
  ((w₀ , w₁ , w₂) , (v₀' , v₁' , v₂'))
  where
    s  = (w₀ ⊕ w₁) ⊕ w₂
    v₀' = ((T₂ ⊗ u₀) ⊕ (T₂ ⊗ w₀)) ⊕ s
    v₁' = ((T₂ ⊗ u₁) ⊕ (T₂ ⊗ w₁)) ⊕ s
    v₂' = ((T₂ ⊗ u₂) ⊕ (T₂ ⊗ w₂)) ⊕ s

-- 定理: waveStepInverse ∘ waveStep = id (左逆)
wave-left-inverse : ∀ u v →
  waveStepInverse (waveStep (u , v)) ≡ (u , v)
wave-left-inverse (u₀ , u₁ , u₂) (v₀ , v₁ , v₂) =
  cong₂ _,_ refl
    (triple-≡
      (wave-inverse-component u₀ v₀ s)
      (wave-inverse-component u₁ v₁ s)
      (wave-inverse-component u₂ v₂ s))
  where s = (u₀ ⊕ u₁) ⊕ u₂

-- 第二分量级引理: 正向恢复 (27 case 穷举)
-- ((T₂⊗b) ⊕ negate(((T₂⊗a) ⊕ (T₂⊗b)) ⊕ c)) ⊕ c = a
wave-inverse-component₂ : ∀ a b c →
  ((T₂ ⊗ b) ⊕ (negate (((T₂ ⊗ a) ⊕ (T₂ ⊗ b)) ⊕ c))) ⊕ c ≡ a
wave-inverse-component₂ T₀ T₀ T₀ = refl
wave-inverse-component₂ T₀ T₀ T₁ = refl
wave-inverse-component₂ T₀ T₀ T₂ = refl
wave-inverse-component₂ T₀ T₁ T₀ = refl
wave-inverse-component₂ T₀ T₁ T₁ = refl
wave-inverse-component₂ T₀ T₁ T₂ = refl
wave-inverse-component₂ T₀ T₂ T₀ = refl
wave-inverse-component₂ T₀ T₂ T₁ = refl
wave-inverse-component₂ T₀ T₂ T₂ = refl
wave-inverse-component₂ T₁ T₀ T₀ = refl
wave-inverse-component₂ T₁ T₀ T₁ = refl
wave-inverse-component₂ T₁ T₀ T₂ = refl
wave-inverse-component₂ T₁ T₁ T₀ = refl
wave-inverse-component₂ T₁ T₁ T₁ = refl
wave-inverse-component₂ T₁ T₁ T₂ = refl
wave-inverse-component₂ T₁ T₂ T₀ = refl
wave-inverse-component₂ T₁ T₂ T₁ = refl
wave-inverse-component₂ T₁ T₂ T₂ = refl
wave-inverse-component₂ T₂ T₀ T₀ = refl
wave-inverse-component₂ T₂ T₀ T₁ = refl
wave-inverse-component₂ T₂ T₀ T₂ = refl
wave-inverse-component₂ T₂ T₁ T₀ = refl
wave-inverse-component₂ T₂ T₁ T₁ = refl
wave-inverse-component₂ T₂ T₁ T₂ = refl
wave-inverse-component₂ T₂ T₂ T₀ = refl
wave-inverse-component₂ T₂ T₂ T₁ = refl
wave-inverse-component₂ T₂ T₂ T₂ = refl

-- 定理: waveStep ∘ waveStepInverse = id (右逆)
wave-right-inverse : ∀ u v →
  waveStep (waveStepInverse (u , v)) ≡ (u , v)
wave-right-inverse (u₀ , u₁ , u₂) (v₀ , v₁ , v₂) =
  cong₂ _,_
    (triple-≡
      (wave-inverse-component₂ u₀ v₀ s)
      (wave-inverse-component₂ u₁ v₁ s)
      (wave-inverse-component₂ u₂ v₂ s))
    refl
  where s = (v₀ ⊕ v₁) ⊕ v₂

--------------------------------------------------------------------------------
-- §5. 能量验证
--
-- 连续波动方程: E = K + V 守恒 (dE/dt = 0)
-- GF(3): 常数态能量为 T₀, 能量守恒是连续投影性质
--
-- 在 GF(3) 中, 波动步进是 729 元素有限集上的置换。
-- 能量函数 E : WaveState → GF(3) 将 729 个状态映射到 3 个值。
-- 置换不一定保持 E — 这是 GF(3) 与 ℝ 的结构差异。
--------------------------------------------------------------------------------

-- 常数态动能为零
kinetic-const-zero : ∀ c →
  kineticEnergy (const-func c , const-func c) ≡ T₀
kinetic-const-zero T₀ = refl
kinetic-const-zero T₁ = refl
kinetic-const-zero T₂ = refl

-- 常数态势能为零 (Δ(const) = 0)
potential-const-zero : ∀ c → potentialEnergy (const-func c) ≡ T₀
potential-const-zero T₀ = refl
potential-const-zero T₁ = refl
potential-const-zero T₂ = refl

-- 常数态总能量为零
energy-const-zero : ∀ c →
  totalEnergy (const-func c , const-func c) ≡ T₀
energy-const-zero T₀ = refl
energy-const-zero T₁ = refl
energy-const-zero T₂ = refl

-- 常数态能量守恒: E(waveStep(const,const)) = E(const,const)
wave-energy-const-conservation : ∀ c →
  totalEnergy (waveStep (const-func c , const-func c)) ≡
  totalEnergy (const-func c , const-func c)
wave-energy-const-conservation T₀ = refl
wave-energy-const-conservation T₁ = refl
wave-energy-const-conservation T₂ = refl

--------------------------------------------------------------------------------
-- §6. 投影丢失总结
--
-- 连续波动方程 (ℝ 上):
--   能量守恒: dE/dt = 0 (精确)
--   时间可逆: u(-t) 也是解
--   无穷维相空间: (u, u_t) ∈ H¹ × L²
--   色散: 不同频率以不同速度传播
--
-- GF(3) 波动方程 (Z/3Z 上):
--   有限置换: 729 个状态上的双射
--   时间可逆: ✓ (wave-left-inverse, wave-right-inverse)
--   能量: 不精确守恒 (GF(3) 无兼容全序, 无正定内积)
--   无色散: 只有 3 个"频率" (GF(3) 上的傅里叶模式)
--   常数态: 平凡不动点, 能量 = T₀
--
-- 截断:
--   能量守恒 → 有限置换 (不保持 GF(3) 值"能量")
--   无穷维 → 729 态
--   连续时间 → 离散步进
--   色散关系 ω(k) → GF(3) 特征值 (至多 3 个)
--
-- 关键洞察:
--   连续能量守恒依赖于 ℝ 的有序域结构 (正定内积, Cauchy-Schwarz)
--   GF(3) 没有兼容全序 (有序域必须 char 0)
--   因此"能量守恒"在 GF(3) 中不是 well-posed 的概念
--   GF(3) 的本源性质是: 有限置换的可逆性 (信息守恒)
--------------------------------------------------------------------------------
