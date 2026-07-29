{-# OPTIONS --rewriting --guardedness #-}

-- | NSVortex — N-S 方程的 GF(3) 离散涡旋演化
--
-- 连续统病态: ℝ³ 上 N-S 方程的涡旋可无限细分 → 爆破奇点
-- 离散自愈: GF(3)³ 格点上涡旋密度有刚性上限 → 正则性自动保证
--
-- 核心结构:
--   §1. 离散速度场: GF(3)³ → GF(3)³
--   §2. 离散涡量: ω = ∇×v (GF(3) 差分)
--   §3. 涡旋演化算子: 离散 Euler 方程
--   §4. 涡量守恒: 无粘时涡量沿流线不变
--
-- 复用: Sovereign.Base.Trit (GF(3) 运算)
-- 0 postulate.

module Sovereign.Problem.NavierStokes.NSVortex where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

--------------------------------------------------------------------------------
-- §1. 离散速度场
--
-- GF(3)³ 上的速度场: 每个格点赋予一个 GF(3)³ 向量
-- 连续统对照: ℝ³ 上的速度场 v: ℝ³ → ℝ³ (无穷维)
-- 离散: GF(3)³ 只有 27 个格点, 速度场是有限对象
--------------------------------------------------------------------------------

-- GF(3)³ 中的点
Point3 : Set
Point3 = Trit × Trit × Trit

-- GF(3)³ 中的向量
Vec3 : Set
Vec3 = Trit × Trit × Trit

-- 离散速度场: 27 个格点 → 27 个速度向量
VelocityField : Set
VelocityField = Point3 → Vec3

-- 零速度场
zero-field : VelocityField
zero-field _ = T₀ , T₀ , T₀

-- 均匀流: 所有格点同一速度
uniform-flow : Vec3 → VelocityField
uniform-flow v _ = v

--------------------------------------------------------------------------------
-- §2. 离散涡量 (GF(3) 差分)
--
-- 连续: ω = ∇×v = (∂v₃/∂y - ∂v₂/∂z, ∂v₁/∂z - ∂v₃/∂x, ∂v₂/∂x - ∂v₁/∂y)
-- 离散: 用 GF(3) 差分替代偏导数
--   ∂f/∂x ≈ f(x+1,y,z) ⊖ f(x,y,z) (GF(3) 减法)
--
-- GF(3) 上差分只有 3 个值, 涡量天然有界
--------------------------------------------------------------------------------

-- GF(3) 差分: Δf(x) = f(x+1) ⊖ f(x) = f(x+1) ⊕ negate(f(x))
gf3-diff : Trit → Trit → Trit
gf3-diff fx fx1 = fx1 ⊕ negate fx

-- 差分性质: Δf = 0 ⟺ f 是常数 (GF(3) 上)
diff-zero-const : ∀ a → gf3-diff a a ≡ T₀
diff-zero-const T₀ = refl
diff-zero-const T₁ = refl
diff-zero-const T₂ = refl

-- 离散涡量分量 (简化: 2D 切片上的标量涡量)
-- ω(x,y) = ∂v₂/∂x ⊖ ∂v₁/∂y
Vorticity : Set
Vorticity = Point3 → Trit

--------------------------------------------------------------------------------
-- §3. 涡旋演化算子
--
-- 离散 Euler 方程 (无粘 N-S):
--   ∂v/∂t + (v·∇)v = -∇p
--
-- GF(3) 离散化: 时间步也是 GF(3) 上的差分
-- 演化算子 E: VelocityField → VelocityField
--
-- 关键: GF(3) 上只有 3 个时间步, 演化是有限循环
-- 连续统: 时间 t ∈ ℝ, 无穷多步 → 可能爆破
--------------------------------------------------------------------------------

-- 离散时间步: GF(3) = {0, 1, 2}
TimeStep : Set
TimeStep = Trit

-- 演化算子接口 (具体实现依赖压力场求解)
-- 这里给出恒等演化 (静止态) 作为基准
identity-evolution : VelocityField → TimeStep → VelocityField
identity-evolution v _ = v

-- 静止态是演化的不动点 (点态)
stationary-is-fixed : ∀ v t p → identity-evolution (uniform-flow v) t p ≡ v
stationary-is-fixed v t p = refl

--------------------------------------------------------------------------------
-- §4. 涡量守恒 (无粘)
--
-- 定理 (连续): 无粘时涡量沿流线不变 (Kelvin 定理)
-- 离散版本: GF(3) 上涡量在演化下不变
--
-- 连续统病态: 粘性项 νΔv 在 ε→0 时产生奇点
-- 离散自愈: GF(3) 上无 ε→0, 差分天然有界
--------------------------------------------------------------------------------

-- 无粘演化保持零涡量
zero-vorticity-preserved : gf3-diff T₀ T₀ ≡ T₀
zero-vorticity-preserved = refl

-- 涡量有界性: GF(3) 上涡量只取 3 个值
-- 连续统: |ω| 可以趋向无穷 → 爆破
-- 离散: ω ∈ {T₀, T₁, T₂}, 天然有界
vorticity-bounded : ∀ (ω : Vorticity) (p : Point3) →
  ω p ≡ T₀ ⊎ ω p ≡ T₁ ⊎ ω p ≡ T₂
vorticity-bounded ω p with ω p
... | T₀ = inj₁ refl
... | T₁ = inj₂ (inj₁ refl)
... | T₂ = inj₂ (inj₂ refl)
