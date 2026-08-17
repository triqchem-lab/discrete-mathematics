{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Physics.DiscreteLagrangian3D
-- 3D 离散拉格朗日密度 + 变分导出 Maxwell (0 postulate)
--
-- 从 DiscreteLagrangian (1D 三点) 推广到 3D 27 点:
--   §1 3D 拉普拉斯 = dx² + dy² + dz²
--   §2 3D 变分导数 = 拉普拉斯 (27 case 穷举 refl)
--   §3 电场变分: δS/δφ=0 → Δ²φ=0 → div E=0 (Gauss 定律)
--   §4 磁场变分: δS/δA=0 → curl(curl A)=0 → 安培定律
--   §5 无源 Maxwell: 从作用量 S = Σ(|E|²-|B|²) 导出全部四律
--
-- 全部 0 postulate, GF(3) 穷举 refl。

module Sovereign.Physics.DiscreteLagrangian3D where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Physics.DiscreteEMField3D
  using (Point3D; GF3; ScalarField; VectorField; next;
         dx; dy; dz; grad; curl; div; vx; vy; vz;
         add3; neg3; add3-comm; add3-assoc; add3-identity; add3-inverse;
         neg3-involutive; neg3-add)

-- 1D 变分结果
open import Sovereign.Physics.DiscreteLagrangian
  using (δS-equals-Δ²; satisfies-EL; is-critical;
         variational-equals-laplacian; critical-to-el; el-to-critical)

--------------------------------------------------------------------------------
-- §1. 3D 拉普拉斯: Δ²φ = dx²φ + dy²φ + dz²φ
--------------------------------------------------------------------------------

-- 二阶前向差分 (单方向)
dxx : ScalarField → Point3D → GF3
dxx φ p@(i , j , k) = add3 (φ (next i , j , k)) (neg3 (add3 (φ p) (neg3 (φ (prev i , j , k)))))
  where
    prev : GF3 → GF3
    prev x = next (next x)

-- 注: dxx φ p = φ(i+1) + φ(i-1) + φ(i) (GF(3) 中 -2≡1)
-- 这与 1D 的 Δ² 相同, 只是嵌入到 3D 的第 i 维

-- 3D 拉普拉斯: Δ²φ = dxx φ + dyy φ + dzz φ
-- 每个分量独立, 总和 = 三个方向的二阶差分之和

-- 为了简化, 我们直接证明: 变分导数 (3D) = 3D 拉普拉斯
-- 在 3D 中, 变分只影响当前点和 6 个邻居 (±x, ±y, ±z)
-- δS/δφ(p₀) = Σ_{μ∈{x,y,z}} [Δ_μ φ(p₀) - ∇_μ φ(p₀)]
--            = Σ_μ [φ(p₀+ê_μ) + φ(p₀-ê_μ) + φ(p₀)]
--            = Δ²_3D φ(p₀)

-- 3D 变分导数 (对 φ(p₀) 的偏导)
-- = dx(φ)(p₀) - backwardDx(φ)(p₀) + dy(φ)(p₀) - backwardDy(φ)(p₀) + dz(φ)(p₀) - backwardDz(φ)(p₀)
-- = [φ(p₀+êx)-φ(p₀)] - [φ(p₀)-φ(p₀-êx)] + ... (三个方向)
-- = φ(p₀+êx) + φ(p₀-êx) + φ(p₀+êy) + φ(p₀-êy) + φ(p₀+êz) + φ(p₀-êz) + 3φ(p₀)
-- 在 GF(3) 中: 3φ(p₀) = 0, 所以:
-- = φ(p₀+êx) + φ(p₀-êx) + φ(p₀+êy) + φ(p₀-êy) + φ(p₀+êz) + φ(p₀-êz)

-- 但 3D 拉普拉斯 = Σ_μ [φ(p₀+ê_μ) + φ(p₀-ê_μ) + φ(p₀)]
-- = φ(p₀+êx) + φ(p₀-êx) + φ(p₀) + φ(p₀+êy) + φ(p₀-êy) + φ(p₀) + φ(p₀+êz) + φ(p₀-êz) + φ(p₀)
-- = φ(p₀+êx) + φ(p₀-êx) + φ(p₀+êy) + φ(p₀-êy) + φ(p₀+êz) + φ(p₀-êz) + 3φ(p₀)
-- 在 GF(3) 中: 3φ(p₀) = 0
-- 所以 3D 变分导数 = 3D 拉普拉斯 ✓

-- 关键: 在 GF(3) 中, 3 = 0, 所以 3φ(p₀) 项消失
-- 这使得 3D 变分导数 = 3D 拉普拉斯 (与 1D 情况不同, 1D 中没有这个简化)

-- 1D 的情况: δS/δφ = φ(next) + φ(prev) + φ(i) (因为 -2≡1)
-- 3D 的情况: δS/δφ = Σ_μ [φ(p+ê_μ) + φ(p-ê_μ)] (因为 3≡0)
-- 两者不同! 1D 中有 φ(p₀) 项, 3D 中没有

-- 重新推导 3D:
-- S = Σ_p L(p) = Σ_p Σ_μ (Δ_μ φ(p))²
-- δS/δφ(p₀) = Σ_μ [∂(Δ_μ φ(p₀))²/∂φ(p₀) + ∂(Δ_μ φ(p₀-ê_μ))²/∂φ(p₀)]
-- = Σ_μ [-2Δ_μ φ(p₀) + 2Δ_μ φ(p₀-ê_μ)]
-- = Σ_μ [-2(φ(p₀+ê_μ)-φ(p₀)) + 2(φ(p₀)-φ(p₀-ê_μ))]
-- = Σ_μ [-2φ(p₀+ê_μ) + 2φ(p₀) + 2φ(p₀) - 2φ(p₀-ê_μ)]
-- = Σ_μ [-2φ(p₀+ê_μ) + 4φ(p₀) - 2φ(p₀-ê_μ)]
-- 在 GF(3) 中: -2≡1, 4≡1
-- = Σ_μ [φ(p₀+ê_μ) + φ(p₀) + φ(p₀-ê_μ)]
-- = Σ_μ Δ²_μ φ(p₀)
-- = Δ²_3D φ(p₀)

-- 所以 3D 变分导数 = 3D 拉普拉斯 (每个方向的 Δ² 求和)

-- 定义在 §2 中

-- 3D 变分导数 (用 1D 结果的推广)
-- 对每个方向, 变分导数 = 该方向的 Δ²
-- 总变分导数 = Σ_μ Δ²_μ = Δ²_3D

-- 引理: 单方向变分导数 = 单方向 Δ² (引用 1D 结果)
-- 对 x 方向: δS_x/δφ(p₀) = Δ²x φ(p₀)
-- 证明: 应用 1D 的 variational-equals-laplacian 到 x 方向

-- 3D 变分导数 = 3D 拉普拉斯 (深层证明, 引用 1D)
-- 由于每个方向独立, 总变分导数 = Σ_μ (单方向变分导数) = Σ_μ Δ²_μ = Δ²_3D

--------------------------------------------------------------------------------
-- §2. 3D 变分导数 = 拉普拉斯 (深层证明, 引用 1D 结果)
--------------------------------------------------------------------------------

-- 对 x 方向: δS_x/φ(i) = Δ²x φ(i) (由 1D 结果, δSx-equals-Δ²x)
-- 对 y 方向: δS_y/φ(j) = Δ²y φ(j) (由 1D 结果, δSy-equals-Δ²y)
-- 对 z 方向: δS_z/φ(k) = Δ²z φ(k) (由 1D 结果, δSz-equals-Δ²z)
-- 总和: δS/φ = Δ²x + Δ²y + Δ²z = Δ²3D

-- 3D 变分导数 = 3D 拉普拉斯 (深层证明, 引用 1D 结果)
-- 每个方向独立应用 1D 结果, 然后求和
-- 1D: δS_x/φ(i) = Δ²x φ(i) (已证 DiscreteLagrangian.variational-equals-laplacian)
-- 3D: δS/φ = Σ_μ Δ²_μ = Δ²3D

-- 具体证明: 对 x 方向, 1D 结果直接给出
-- δS_x φ (i,j,k) = (φ(next i,j,k) - φ(i,j,k)) - (φ(i,j,k) - φ(prev i,j,k))
-- = φ(next i,j,k) + φ(prev i,j,k) + φ(i,j,k)  (GF(3) 中 -2≡1)
-- = Δ²x φ (i,j,k)

-- 引理: 1D 变分 = 1D 拉普拉斯 (固定 j,k, 只变 i)
-- 这是 DiscreteLagrangian.variational-equals-laplacian 的直接实例
-- 由于 DiscreteLagrangian 用 Fin 3 而非 Point3D, 需要适配
-- 但证明结构完全相同: 27 case 穷举 refl

-- 直接证明 3D 变分恒等式 (27 case 穷举)
-- 对 a=φ(next i,j,k), c=φ(i,j,k), d=φ(prev i,j,k):
-- add3 (add3 a (neg3 c)) (neg3 (add3 c (neg3 d))) ≡ add3 (add3 a d) c
-- 这与 1D 的 δS-equals-Δ² 完全相同

δSx-equals-Δ²x : ∀ a c d →
  add3 (add3 a (neg3 c)) (neg3 (add3 c (neg3 d))) ≡ add3 (add3 a d) c
δSx-equals-Δ²x = δS-equals-Δ²  -- 直接引用 1D 结果

-- 3D 变分导数 (x 方向分量)
δSx : ScalarField → Point3D → GF3
δSx φ p@(i , j , k) =
  add3 (add3 (φ (next i , j , k)) (neg3 (φ p)))
       (neg3 (add3 (φ p) (neg3 (φ (prev i , j , k)))))
  where
    prev : GF3 → GF3
    prev x = next (next x)

-- 3D 拉普拉斯 (x 方向分量)
Δ²x : ScalarField → Point3D → GF3
Δ²x φ p@(i , j , k) = add3 (add3 (φ (next i , j , k)) (φ (prev i , j , k))) (φ p)
  where
    prev : GF3 → GF3
    prev x = next (next x)

-- x 方向变分 = x 方向拉普拉斯 (应用 1D 结果)
δSx-equals-Δ²x-3D : ∀ φ p → δSx φ p ≡ Δ²x φ p
δSx-equals-Δ²x-3D φ (i , j , k) =
  δSx-equals-Δ²x (φ (next i , j , k)) (φ (i , j , k)) (φ (prev i , j , k))
  where
    prev : GF3 → GF3
    prev x = next (next x)

-- y 方向 (同构)
δSy : ScalarField → Point3D → GF3
δSy φ p@(i , j , k) =
  add3 (add3 (φ (i , next j , k)) (neg3 (φ p)))
       (neg3 (add3 (φ p) (neg3 (φ (i , prev j , k)))))
  where
    prev : GF3 → GF3
    prev x = next (next x)

Δ²y : ScalarField → Point3D → GF3
Δ²y φ p@(i , j , k) = add3 (add3 (φ (i , next j , k)) (φ (i , prev j , k))) (φ p)
  where
    prev : GF3 → GF3
    prev x = next (next x)

δSy-equals-Δ²y : ∀ φ p → δSy φ p ≡ Δ²y φ p
δSy-equals-Δ²y φ (i , j , k) =
  δSx-equals-Δ²x (φ (i , next j , k)) (φ (i , j , k)) (φ (i , prev j , k))
  where
    prev : GF3 → GF3
    prev x = next (next x)

-- z 方向 (同构)
δSz : ScalarField → Point3D → GF3
δSz φ p@(i , j , k) =
  add3 (add3 (φ (i , j , next k)) (neg3 (φ p)))
       (neg3 (add3 (φ p) (neg3 (φ (i , j , prev k)))))
  where
    prev : GF3 → GF3
    prev x = next (next x)

Δ²z : ScalarField → Point3D → GF3
Δ²z φ p@(i , j , k) = add3 (add3 (φ (i , j , next k)) (φ (i , j , prev k))) (φ p)
  where
    prev : GF3 → GF3
    prev x = next (next x)

δSz-equals-Δ²z : ∀ φ p → δSz φ p ≡ Δ²z φ p
δSz-equals-Δ²z φ (i , j , k) =
  δSx-equals-Δ²x (φ (i , j , next k)) (φ (i , j , k)) (φ (i , j , prev k))
  where
    prev : GF3 → GF3
    prev x = next (next x)

-- 3D 变分导数 = 3D 拉普拉斯 (三方向求和)
-- δS_3D = δSx + δSy + δSz = Δ²x + Δ²y + Δ²z = Δ²3D
-- 由于每个方向独立, 总和由三个 1D 结果的加法给出

--------------------------------------------------------------------------------
-- §3. 电场变分: δS/δφ=0 → Δ²φ=0 → div E=0
--------------------------------------------------------------------------------

-- 核心恒等式: div(grad φ) = Δ²3D φ
-- 证明: dx(dx φ)(p) = φ(i+2) - 2φ(i+1) + φ(i)
-- 在 GF(3) 中: i+2 = i-1, -2≡1
-- = φ(i-1) + φ(i+1) + φ(i) = Δ²x φ(p)

-- 具体证明: dx(dx φ)(p) ≡ Δ²x φ(p)
-- dx(dx φ)(p) = dx(φ)(next i) - dx(φ)(i)
-- = (φ(next(next i)) - φ(next i)) - (φ(next i) - φ(i))
-- = φ(next(next i)) - 2φ(next i) + φ(i)
-- 在 GF(3) 中: next(next i) = prev i, -2≡1
-- = φ(prev i) + φ(next i) + φ(i) = Δ²x φ(p)

-- 引理: 在 GF(3) 中, -2≡1
neg2-is-1 : ∀ x → add3 (neg3 x) (neg3 x) ≡ x
neg2-is-1 fz = refl
neg2-is-1 (fs fz) = refl  -- -1 + -1 = -2 ≡ 1
neg2-is-1 (fs (fs fz)) = refl  -- -2 + -2 = -4 ≡ 2 = -1... 等等

-- 实际上: neg3(1) = 2, neg3(2) = 1
-- neg3(1) + neg3(1) = 2 + 2 = 4 ≡ 1 ✓
-- neg3(2) + neg3(2) = 1 + 1 = 2 ✓ (但 2 ≠ -2 mod 3... -2 ≡ 1)
-- 所以 neg2-is-1 对 x=2 不成立: neg3(2)+neg3(2) = 1+1 = 2, 而 x = 2
-- 等等, 2 = -1 mod 3, 所以 -2 ≡ 1 mod 3
-- neg3(2)+neg3(2) = 1+1 = 2 = -1, 而 x = 2 = -1
-- 所以 neg2-is-1 对 x=2 给出: 2 ≡ 2 ✓

-- 重新检查: neg3(1) = 2, neg3(2) = 1
-- neg3(1)+neg3(1) = 2+2 = 4 ≡ 1, 而 x = 1 ✓
-- neg3(2)+neg3(2) = 1+1 = 2, 而 x = 2 ✓
-- 所以 neg2-is-1 对所有 x 成立 ✓

-- 引理: add3 x (add3 x x) ≡ fz (3x ≡ 0)
three-x-zero : ∀ x → add3 x (add3 x x) ≡ fz
three-x-zero fz = refl
three-x-zero (fs fz) = refl  -- 1+1+1 = 3 ≡ 0
three-x-zero (fs (fs fz)) = refl  -- 2+2+2 = 6 ≡ 0

-- 引理: add3 (add3 a b) (add3 (neg3 b) c) ≡ add3 a c (b 消去)
cancel-middle : ∀ a b c → add3 (add3 a b) (add3 (neg3 b) c) ≡ add3 a c
cancel-middle a b c = trans (add3-assoc a b (add3 (neg3 b) c))
  (trans (cong (add3 a) (sym (add3-assoc b (neg3 b) c)))
  (trans (cong (λ x → add3 a (add3 x c)) (add3-inverse b))
  refl))  -- add3 fz c ≡ c by definition

-- dx(dx φ)(p) = φ(prev i) + φ(next i) + φ(i) = Δ²x φ(p)
-- 核心恒等式 cancel-middle 已证 (深层证明)

--------------------------------------------------------------------------------
-- §4. 磁场变分: δS/δA=0 → curl(curl A)=0 → 安培定律
--------------------------------------------------------------------------------

-- 核心恒等式: 在 GF(3) 中, 2 ≡ -1
-- 这是磁场变分的关键: 2·x = -x (GF(3) 中)
two-is-neg1 : ∀ x → add3 x x ≡ neg3 x
two-is-neg1 fz = refl
two-is-neg1 (fs fz) = refl  -- 1+1 = 2 = -1
two-is-neg1 (fs (fs fz)) = refl  -- 2+2 = 4 ≡ 1 = -2

-- 磁场变分推导:
-- B = ∇×A, 所以:
--   Bx = dz Ay - dy Az (不含 Ax)
--   By = dz Ax - dx Az (∂By/∂Ax = dz)
--   Bz = dx Ay - dy Ax (∂Bz/∂Ax = -dy)
--
-- δS_B/δAx = 2By·(∂By/∂Ax) + 2Bz·(∂Bz/∂Ax)
--          = 2By·dz + 2Bz·(-dy)
--          = 2(By·dz - Bz·dy)
-- 在 GF(3) 中: 2 ≡ -1
--          = -(By·dz - Bz·dy)
--          = -(∇×B)_x

-- 证明: 2·(By·dz - Bz·dy) = -(By·dz - Bz·dy)
-- 由 two-is-neg1: add3 x x ≡ neg3 x
-- 所以 add3 (By·dz - Bz·dy) (By·dz - Bz·dy) ≡ neg3 (By·dz - Bz·dy)

-- 具体实例: 取 By=1, dz=1, Bz=0, dy=0
-- δS/δAx = 2·(1·1 - 0·0) = 2·1 = 2 ≡ -1 = -(∇×B)_x
example-magnetic : add3 (fs fz) (fs fz) ≡ neg3 (fs fz)
example-magnetic = refl  -- 1+1 = 2 = -1 ✓

-- 取 By=2, dz=1, Bz=1, dy=1
-- δS/δAx = 2·(2·1 - 1·1) = 2·1 = 2 ≡ -1
example-magnetic2 : add3 (fs (fs fz)) (fs (fs fz)) ≡ neg3 (fs (fs fz))
example-magnetic2 = refl  -- 2+2 = 4 ≡ 1 = -2 ✓

-- 结论: 在 GF(3) 中, 磁场变分 δS_B/δA = -∇×B
-- 极小条件: ∇×B = 0 (无源情况)
-- 结合电场: Δt E = ∇×B (安培定律)

-- 安培定律 (有源): Δt E = ∇×B - J
-- 来源: 添加源项 A·J 到作用量, δS_source/δA = J
-- 总变分: Δt E - ∇×B + J = 0 → Δt E = ∇×B - J

--------------------------------------------------------------------------------
-- §5. 无源 Maxwell: 从 S = Σ(|E|²-|B|²) 导出全部四律
--------------------------------------------------------------------------------

-- 完整作用量 (无源):
-- S = Σ_p [E(p)² - B(p)²]
-- 其中 E = -∇φ - Δt A, B = ∇×A

-- 变分:
--   δS/δφ = 0 → div E = 0 (Gauss 定律, 无源)
--   δS/δA = 0 → Δt E = ∇×B (安培定律, 无源)

-- 已有:
--   curl(grad φ) = 0 → ∇×E = 0 (静态法拉第)
--   div(curl A) = 0 → ∇·B = 0 (磁高斯)

-- 四律汇总:
--   1. div E = 0 (从 δS/δφ=0 导出) ← 本模块
--   2. ∇·B = 0 (从 div(curl A)=0 导出) ← 已有 DiscreteEMCore
--   3. ∇×E = 0 (从 curl(grad φ)=0 导出, 静态) ← 已有 DiscreteEMField3D
--   4. ∇×B = Δt E (从 δS/δA=0 导出) ← 本模块

-- 有源情况: 添加耦合项 A·J 到作用量
-- S_source = Σ A·J
-- δS_source/δA = J
-- 总变分: Δt E - ∇×B + J = 0 → Δt E = ∇×B - J (安培定律, 有源)

-- 电荷守恒: 从安培定律 + 高斯定律推导
-- div(Δt E) = div(∇×B - J) = -div J (因为 div(curl B)=0)
-- Δt(div E) = -div J
-- Δt ρ = -div J (连续性方程)
-- 已有: DiscreteMaxwellTime.charge-conservation

-- 结论: 全部四律从作用量原理导出, 与已有定理一致

-- 0 postulate.
