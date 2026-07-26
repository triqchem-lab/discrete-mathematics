{-# OPTIONS --rewriting #-}
module Sovereign.PDE.HeatEquationDiscrete where

--------------------------------------------------------------------------------
-- GF(3) 离散热方程 — MSC 35K05 (热方程) 的离散本源
--
-- 连续热方程: ∂u/∂t = Δu (耗散, 能量单调递减, 趋向平衡)
-- GF(3) 热方程: u_{n+1} = u_n + Δ_L u_n (周期 3, 能量循环, 无耗散)
--
-- 核心发现:
--   1. 离散 Laplace 在 Z/3Z 上等于 Δ² (二阶差分)
--      因为 -2 ≡ 1 (mod 3), 所以 Δ_L u(i) = u(i+1)+u(i-1)+u(i) = sum3(u)
--   2. 热步进周期 3: heatStep³ ≡ id (连续热方程无此性质)
--   3. 能量不耗散而是循环: E(step u) = E(u) + 2·s² (GF(3))
--   4. 连续耗散是 GF(3) 周期性的"不存在的极限"投影
--
-- 依赖:
--   Trit: GF(3) 代数
--   ProjectionDifferential: Δ, sum3, GF3Func
--   DiscreteDE: evalGF3, tabulate
--
-- 0 postulate — 全部构造性证明 (穷举法)
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (
  _≡_; _≢_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; ⊕-identityʳ)
open import Sovereign.Algebra.ProjectionDifferential using (
  GF3Func; Δ; sum3; const-func; Δ²-is-const; Δ-const-zero)
open import Sovereign.Algebra.DiscreteDE using (
  evalGF3; tabulate)

--------------------------------------------------------------------------------
-- §1. 一维格点函数 Grid1D
--
-- Grid1D N = Fin N → Trit 是 N 点格点上的 GF(3) 值函数。
-- 对于 GF(3) 本源证明,  specialize 到 N = 3 (Z/3Z 循环格点),
-- 此时 Grid1D 3 ≅ GF3Func = Trit × Trit × Trit。
--
-- 使用 GF3Func 而非 Fin 3 → Trit 避免函数外延性公理。
--------------------------------------------------------------------------------

Grid1D : ℕ → Set
Grid1D N = Fin N → Trit

-- Grid1D 3 → GF3Func 桥接
grid1d3-to-gf3func : Grid1D 3 → GF3Func
grid1d3-to-gf3func f = (f zero , f (suc zero) , f (suc (suc zero)))

-- GF3Func → Grid1D 3 桥接
gf3func-to-grid1d3 : GF3Func → Grid1D 3
gf3func-to-grid1d3 (a , b , c) zero          = a
gf3func-to-grid1d3 (a , b , c) (suc zero)    = b
gf3func-to-grid1d3 (a , b , c) (suc (suc zero)) = c

-- GF3Func 上的逐点加法
_⊕g_ : GF3Func → GF3Func → GF3Func
(a₀ , a₁ , a₂) ⊕g (b₀ , b₁ , b₂) = (a₀ ⊕ b₀ , a₁ ⊕ b₁ , a₂ ⊕ b₂)

--------------------------------------------------------------------------------
-- §2. 离散 Laplace 算子
--
-- 连续 Laplace: Δ_L u(i) = u(i+1) + u(i-1) - 2u(i)
-- GF(3) 中: -2 ≡ 1 (mod 3), 所以 -2u(i) = u(i)
-- 因此: Δ_L u(i) = u(i+1) + u(i-1) + u(i) = sum3(u) (对所有 i)
--
-- 关键定理: 在 Z/3Z 上, 离散 Laplace = Δ² (二阶差分)
-- 这是 GF(3) 特征 3 的直接推论。
--------------------------------------------------------------------------------

-- GF(3) 平方函数
sq : Trit → Trit
sq x = x ⊗ x

-- 离散 Laplace 算子 (Z/3Z 周期边界)
-- Δ_L u(i) = u(i+1) ⊕ u(i-1) ⊕ u(i) = sum3(u) (GF(3) 中 -2≡1)
laplacian : GF3Func → GF3Func
laplacian u = (sum3 u , sum3 u , sum3 u)

-- 定理: 离散 Laplace = Δ² (二阶差分)
-- 代数本质: 在 char 3 上, -2 = 1, 所以 Laplace 退化为求和
laplacian≡Δ² : ∀ u → laplacian u ≡ Δ (Δ u)
laplacian≡Δ² u = sym (Δ²-is-const u)

-- 常数函数的 Laplace 为零
-- sum3(c,c,c) = c⊕c⊕c = 3c = 0 (GF(3) 中 3=0)
laplacian-const-zero : ∀ c → laplacian (const-func c) ≡ (T₀ , T₀ , T₀)
laplacian-const-zero T₀ = refl
laplacian-const-zero T₁ = refl
laplacian-const-zero T₂ = refl

--------------------------------------------------------------------------------
-- §3. 热方程步进
--
-- 连续: u_{n+1} = u_n + dt·Δ_L u_n (dt → 0 极限)
-- GF(3): u_{n+1}(i) = u_n(i) ⊕ Δ_L u_n(i) (dt = T₁, 固定步长)
--
-- 由于 Δ_L u = (s,s,s), 热步进将每个格点值加上 sum3(u)。
--------------------------------------------------------------------------------

-- 热方程步进 (dt = T₁)
heatStep : GF3Func → GF3Func
heatStep (u₀ , u₁ , u₂) = (u₀ ⊕ s , u₁ ⊕ s , u₂ ⊕ s)
  where s = (u₀ ⊕ u₁) ⊕ u₂

-- 热步进 = 恒等 + Laplace
heatStep≡id⊕Δ : ∀ u → heatStep u ≡ u ⊕g laplacian u
heatStep≡id⊕Δ (T₀ , T₀ , T₀) = refl
heatStep≡id⊕Δ (T₀ , T₀ , T₁) = refl
heatStep≡id⊕Δ (T₀ , T₀ , T₂) = refl
heatStep≡id⊕Δ (T₀ , T₁ , T₀) = refl
heatStep≡id⊕Δ (T₀ , T₁ , T₁) = refl
heatStep≡id⊕Δ (T₀ , T₁ , T₂) = refl
heatStep≡id⊕Δ (T₀ , T₂ , T₀) = refl
heatStep≡id⊕Δ (T₀ , T₂ , T₁) = refl
heatStep≡id⊕Δ (T₀ , T₂ , T₂) = refl
heatStep≡id⊕Δ (T₁ , T₀ , T₀) = refl
heatStep≡id⊕Δ (T₁ , T₀ , T₁) = refl
heatStep≡id⊕Δ (T₁ , T₀ , T₂) = refl
heatStep≡id⊕Δ (T₁ , T₁ , T₀) = refl
heatStep≡id⊕Δ (T₁ , T₁ , T₁) = refl
heatStep≡id⊕Δ (T₁ , T₁ , T₂) = refl
heatStep≡id⊕Δ (T₁ , T₂ , T₀) = refl
heatStep≡id⊕Δ (T₁ , T₂ , T₁) = refl
heatStep≡id⊕Δ (T₁ , T₂ , T₂) = refl
heatStep≡id⊕Δ (T₂ , T₀ , T₀) = refl
heatStep≡id⊕Δ (T₂ , T₀ , T₁) = refl
heatStep≡id⊕Δ (T₂ , T₀ , T₂) = refl
heatStep≡id⊕Δ (T₂ , T₁ , T₀) = refl
heatStep≡id⊕Δ (T₂ , T₁ , T₁) = refl
heatStep≡id⊕Δ (T₂ , T₁ , T₂) = refl
heatStep≡id⊕Δ (T₂ , T₂ , T₀) = refl
heatStep≡id⊕Δ (T₂ , T₂ , T₁) = refl
heatStep≡id⊕Δ (T₂ , T₂ , T₂) = refl

--------------------------------------------------------------------------------
-- §4. 能量泛函
--
-- 连续: E(u) = ∫ u² dx (正定, 单调递减)
-- GF(3): E(u) = Σ u(i)² (GF(3) 值, 非正定, 循环)
--
-- 在 GF(3) 中: 0²=0, 1²=1, 2²=1
-- 所以 sq(x) = 0 当且仅当 x = 0, 否则为 1。
-- E(u) = (非零格点数) mod 3。
--------------------------------------------------------------------------------

-- GF(3) 能量泛函
energy : GF3Func → Trit
energy (a , b , c) = (sq a ⊕ sq b) ⊕ sq c

-- 平方函数的性质
sq-zero : sq T₀ ≡ T₀
sq-zero = refl

sq-one : sq T₁ ≡ T₁
sq-one = refl

sq-two : sq T₂ ≡ T₁
sq-two = refl

-- 平方消灭 negate: sq(-x) = sq(x)
sq-negate : ∀ x → sq (negate x) ≡ sq x
sq-negate T₀ = refl
sq-negate T₁ = refl
sq-negate T₂ = refl

--------------------------------------------------------------------------------
-- §5. 常数稳态: Δ(const) = 0
--
-- 连续: Δ(c) = 0 (常数函数的 Laplace 为零)
-- GF(3): sum3(c,c,c) = 3c = 0 (char 3)
--
-- 推论: heatStep(const c) = const c (常数是热方程不动点)
--------------------------------------------------------------------------------

-- 常数稳态: heatStep(const c) = const c
heat-const-steady : ∀ c → heatStep (const-func c) ≡ const-func c
heat-const-steady T₀ = refl
heat-const-steady T₁ = refl
heat-const-steady T₂ = refl

--------------------------------------------------------------------------------
-- §6. 能量演化恒等式 — GF(3) 耗散律
--
-- 连续: dE/dt = -2∫|∇u|² dx ≤ 0 (能量单调递减)
-- GF(3): E(step u) = E(u) ⊕ T₂ ⊗ s² (精确代数恒等式)
--   其中 s = sum3(u)
--
-- 推论:
--   s = 0 (平衡态): E 守恒
--   s ≠ 0 (非平衡): E 变化 T₂ (= -1 mod 3)
--
-- 这不是耗散, 而是周期 3 循环!
--------------------------------------------------------------------------------

-- 能量演化恒等式 (27 case 穷举)
energy-step-identity : ∀ u →
  energy (heatStep u) ≡ energy u ⊕ (T₂ ⊗ sq (sum3 u))
energy-step-identity (T₀ , T₀ , T₀) = refl
energy-step-identity (T₀ , T₀ , T₁) = refl
energy-step-identity (T₀ , T₀ , T₂) = refl
energy-step-identity (T₀ , T₁ , T₀) = refl
energy-step-identity (T₀ , T₁ , T₁) = refl
energy-step-identity (T₀ , T₁ , T₂) = refl
energy-step-identity (T₀ , T₂ , T₀) = refl
energy-step-identity (T₀ , T₂ , T₁) = refl
energy-step-identity (T₀ , T₂ , T₂) = refl
energy-step-identity (T₁ , T₀ , T₀) = refl
energy-step-identity (T₁ , T₀ , T₁) = refl
energy-step-identity (T₁ , T₀ , T₂) = refl
energy-step-identity (T₁ , T₁ , T₀) = refl
energy-step-identity (T₁ , T₁ , T₁) = refl
energy-step-identity (T₁ , T₁ , T₂) = refl
energy-step-identity (T₁ , T₂ , T₀) = refl
energy-step-identity (T₁ , T₂ , T₁) = refl
energy-step-identity (T₁ , T₂ , T₂) = refl
energy-step-identity (T₂ , T₀ , T₀) = refl
energy-step-identity (T₂ , T₀ , T₁) = refl
energy-step-identity (T₂ , T₀ , T₂) = refl
energy-step-identity (T₂ , T₁ , T₀) = refl
energy-step-identity (T₂ , T₁ , T₁) = refl
energy-step-identity (T₂ , T₁ , T₂) = refl
energy-step-identity (T₂ , T₂ , T₀) = refl
energy-step-identity (T₂ , T₂ , T₁) = refl
energy-step-identity (T₂ , T₂ , T₂) = refl

-- 推论: 平衡态 (sum3=0) 能量守恒
energy-conservation-balanced : ∀ u → sum3 u ≡ T₀ →
  energy (heatStep u) ≡ energy u
energy-conservation-balanced u h rewrite energy-step-identity u | h =
  ⊕-identityʳ (energy u)

--------------------------------------------------------------------------------
-- §7. 热步进周期 3 — GF(3) 特有性质
--
-- 连续热方程: u(t) → 平衡态 (t → ∞), 不可逆
-- GF(3) 热方程: heatStep³ ≡ id, 完全可逆, 周期 3
--
-- 代数本质: heatStep(u) = u + s, s 在步进下不变 (sum3(u+s) = s+3s = s)
-- 所以: u → u+s → u+2s → u+3s = u (因为 3=0 in GF(3))
--
-- 这是连续耗散的"不存在的极限"的离散本源:
-- 连续 e^{-λt} 衰减 → 离散 C₃ 循环群作用
--------------------------------------------------------------------------------

-- 热步进周期 3 (27 case 穷举)
heatStep³≡id : ∀ u → heatStep (heatStep (heatStep u)) ≡ u
heatStep³≡id (T₀ , T₀ , T₀) = refl
heatStep³≡id (T₀ , T₀ , T₁) = refl
heatStep³≡id (T₀ , T₀ , T₂) = refl
heatStep³≡id (T₀ , T₁ , T₀) = refl
heatStep³≡id (T₀ , T₁ , T₁) = refl
heatStep³≡id (T₀ , T₁ , T₂) = refl
heatStep³≡id (T₀ , T₂ , T₀) = refl
heatStep³≡id (T₀ , T₂ , T₁) = refl
heatStep³≡id (T₀ , T₂ , T₂) = refl
heatStep³≡id (T₁ , T₀ , T₀) = refl
heatStep³≡id (T₁ , T₀ , T₁) = refl
heatStep³≡id (T₁ , T₀ , T₂) = refl
heatStep³≡id (T₁ , T₁ , T₀) = refl
heatStep³≡id (T₁ , T₁ , T₁) = refl
heatStep³≡id (T₁ , T₁ , T₂) = refl
heatStep³≡id (T₁ , T₂ , T₀) = refl
heatStep³≡id (T₁ , T₂ , T₁) = refl
heatStep³≡id (T₁ , T₂ , T₂) = refl
heatStep³≡id (T₂ , T₀ , T₀) = refl
heatStep³≡id (T₂ , T₀ , T₁) = refl
heatStep³≡id (T₂ , T₀ , T₂) = refl
heatStep³≡id (T₂ , T₁ , T₀) = refl
heatStep³≡id (T₂ , T₁ , T₁) = refl
heatStep³≡id (T₂ , T₁ , T₂) = refl
heatStep³≡id (T₂ , T₂ , T₀) = refl
heatStep³≡id (T₂ , T₂ , T₁) = refl
heatStep³≡id (T₂ , T₂ , T₂) = refl

-- sum3 在热步进下不变
sum3-heatStep-invariant : ∀ u → sum3 (heatStep u) ≡ sum3 u
sum3-heatStep-invariant (T₀ , T₀ , T₀) = refl
sum3-heatStep-invariant (T₀ , T₀ , T₁) = refl
sum3-heatStep-invariant (T₀ , T₀ , T₂) = refl
sum3-heatStep-invariant (T₀ , T₁ , T₀) = refl
sum3-heatStep-invariant (T₀ , T₁ , T₁) = refl
sum3-heatStep-invariant (T₀ , T₁ , T₂) = refl
sum3-heatStep-invariant (T₀ , T₂ , T₀) = refl
sum3-heatStep-invariant (T₀ , T₂ , T₁) = refl
sum3-heatStep-invariant (T₀ , T₂ , T₂) = refl
sum3-heatStep-invariant (T₁ , T₀ , T₀) = refl
sum3-heatStep-invariant (T₁ , T₀ , T₁) = refl
sum3-heatStep-invariant (T₁ , T₀ , T₂) = refl
sum3-heatStep-invariant (T₁ , T₁ , T₀) = refl
sum3-heatStep-invariant (T₁ , T₁ , T₁) = refl
sum3-heatStep-invariant (T₁ , T₁ , T₂) = refl
sum3-heatStep-invariant (T₁ , T₂ , T₀) = refl
sum3-heatStep-invariant (T₁ , T₂ , T₁) = refl
sum3-heatStep-invariant (T₁ , T₂ , T₂) = refl
sum3-heatStep-invariant (T₂ , T₀ , T₀) = refl
sum3-heatStep-invariant (T₂ , T₀ , T₁) = refl
sum3-heatStep-invariant (T₂ , T₀ , T₂) = refl
sum3-heatStep-invariant (T₂ , T₁ , T₀) = refl
sum3-heatStep-invariant (T₂ , T₁ , T₁) = refl
sum3-heatStep-invariant (T₂ , T₁ , T₂) = refl
sum3-heatStep-invariant (T₂ , T₂ , T₀) = refl
sum3-heatStep-invariant (T₂ , T₂ , T₁) = refl
sum3-heatStep-invariant (T₂ , T₂ , T₂) = refl

--------------------------------------------------------------------------------
-- §8. GF(3) 序与能量耗散
--
-- GF(3) 没有与域结构兼容的全序 (有序域必须是 char 0)。
-- 但我们可以定义"规范序" T₀ < T₁ < T₂ 作为集合论序。
--
-- 在此序下:
--   E(u) ≠ T₀ 时: E(step u) ≤₃ E(u) (能量递减或不变)
--   E(u) = T₀ 且 sum3(u) ≠ 0 时: E(step u) = T₂ > T₀ (环绕)
--
-- 连续耗散 E(t) → 0 是 GF(3) 周期循环的"不存在的极限"投影。
--------------------------------------------------------------------------------

-- GF(3) 规范序
data _≤₃_ : Trit → Trit → Set where
  0≤₀ : T₀ ≤₃ T₀
  0≤₁ : T₀ ≤₃ T₁
  0≤₂ : T₀ ≤₃ T₂
  1≤₁ : T₁ ≤₃ T₁
  1≤₂ : T₁ ≤₃ T₂
  2≤₂ : T₂ ≤₃ T₂

-- 序自反性
≤₃-refl : ∀ x → x ≤₃ x
≤₃-refl T₀ = 0≤₀
≤₃-refl T₁ = 1≤₁
≤₃-refl T₂ = 2≤₂

-- T₂ 加法递减: x ≠ 0 时, x + T₂ ≤₃ x
-- T₁ ⊕ T₂ = T₀ ≤₃ T₁; T₂ ⊕ T₂ = T₁ ≤₃ T₂
⊕T₂-decreases : ∀ x → x ≢ T₀ → (x ⊕ T₂) ≤₃ x
⊕T₂-decreases T₀ ne = ⊥-elim (ne refl)
⊕T₂-decreases T₁ _  = 0≤₁
⊕T₂-decreases T₂ _  = 1≤₂

-- 能量耗散核心引理: 对任意能量值 e 和 sum3 值 s
dissipation-core : ∀ e s → e ≢ T₀ → (e ⊕ (T₂ ⊗ sq s)) ≤₃ e
dissipation-core T₀ T₀ ne = ⊥-elim (ne refl)
dissipation-core T₀ T₁ ne = ⊥-elim (ne refl)
dissipation-core T₀ T₂ ne = ⊥-elim (ne refl)
dissipation-core T₁ T₀ _  = 1≤₁  -- E ⊕ 0 = E
dissipation-core T₁ T₁ _  = 0≤₁  -- E ⊕ T₂ = T₀ ≤₃ T₁
dissipation-core T₁ T₂ _  = 0≤₁  -- E ⊕ T₂ = T₀ ≤₃ T₁
dissipation-core T₂ T₀ _  = 2≤₂  -- E ⊕ 0 = E
dissipation-core T₂ T₁ _  = 1≤₂  -- E ⊕ T₂ = T₁ ≤₃ T₂
dissipation-core T₂ T₂ _  = 1≤₂  -- E ⊕ T₂ = T₁ ≤₃ T₂

-- 定理: 能量耗散 (GF(3) 序下)
-- 当 E(u) ≠ T₀ 时, E(heatStep u) ≤₃ E(u)
heat-dissipation : ∀ u → energy u ≢ T₀ → energy (heatStep u) ≤₃ energy u
heat-dissipation u ne =
  subst (λ x → x ≤₃ energy u)
        (sym (energy-step-identity u))
        (dissipation-core (energy u) (sum3 u) ne)

--------------------------------------------------------------------------------
-- §9. 投影丢失总结
--
-- 连续热方程 (ℝ 上):
--   耗散: dE/dt ≤ 0, E(t) → 0 (t → ∞)
--   不可逆: 信息丢失, 趋向热力学平衡
--   无穷时间渐近: u(t) → 常数
--
-- GF(3) 热方程 (Z/3Z 上):
--   周期: heatStep³ = id, 完全可逆
--   能量循环: E → E⊕T₂ → E⊕T₁ → E (周期 3)
--   无渐近: 不趋向平衡, 而是永恒循环
--   有限状态: 27 个格点函数, 热步进是 S₂₇ 中的置换
--
-- 截断:
--   耗散 → 周期 (e^{-λt} → C₃ 群作用)
--   不可逆 → 可逆 (信息守恒)
--   无穷维 → 27 态
--   连续时间 → 离散周期
--------------------------------------------------------------------------------
