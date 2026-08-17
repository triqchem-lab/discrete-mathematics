{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.DynamicMagicSquare
-- 动态幻方: 矢量方向动态系统 (本体类型, 卢先生定义)
--
-- 幻方不是静态数字排列, 而是过程:
--   n 阶 = n 个矢量方向同时变化
--   套环 = 每个方向在环上转 (基座环 GF(3), +1 归零周期 3)
--   动态 = 所有方向在同一时间参数 t 下同步演化
--   解   = 闭合约束下的全部轨线
-- 传统数字幻方 = 此动态过程在某一时刻的投影切片 (电影的一帧)。
--
-- 与既有模块的连接:
--   基座层: SP2Ternary.agda (+1 归零周期 3 / ×2 乌比斯环周期 2 永不归零)
--   观测层: GF4AffineMagicSquare.affine-trajectory / GF9AffineMagicSquare.trajectory-Lλ
--          (环同步转动经仿射投影为步长 (a+b)/(λ+1) 的平移)
--   静态实例: OrthogonalLatinSquare.agda (M4 完全幻方 = 动态过程的一帧)
--
-- 包含:
--   §1 矢量方向与套环 (类型)
--   §2 动态解 = 轨道 (同步演化) + 静动区分定理
--   §3 两条基座轨道的周期/归零性质
--   §4 卢先生阶数序列 3,5,8,13,21,34,55,89,144 (斐波那契递推 + 144=POLAR_WINDING 锚定)

module Sovereign.Structology.DynamicMagicSquare where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Base.Invariants using (POLAR_WINDING)

--------------------------------------------------------------------------------
-- §1. n 个矢量方向同时变化
--------------------------------------------------------------------------------

-- 方向索引集: n 阶 = n 个矢量方向
VectorDirections : ℕ → Set
VectorDirections n = Fin n

-- 套环: 每个方向在一个 3 态环 (基座 GF(3)) 上变化
NestedRings : ℕ → Set
NestedRings n = Fin n → Trit

--------------------------------------------------------------------------------
-- §2. 动态解 = 轨道 (同步演化)
--------------------------------------------------------------------------------

-- 轨道: 时间 t ↦ 该时刻 n 个环的组态
Orbit : ℕ → Set
Orbit n = ℕ → NestedRings n

-- 动态幻方 (本体类型): 阶数 + 轨道
-- 解是整条轨道, 不是单个静组态
record DynamicMagicSquare : Set where
  field
    n : ℕ          -- n 阶 = n 个矢量方向同时变化
    orbit : Orbit n

-- 静态投影切片: t 时刻快照 (传统数字幻方 = 这样的一帧)
snapshot : (dm : DynamicMagicSquare) → ℕ → NestedRings (DynamicMagicSquare.n dm)
snapshot dm t = DynamicMagicSquare.orbit dm t

--------------------------------------------------------------------------------
-- §3. 两条基座轨道: +1 归零 (周期 3) vs ×2 乌比斯环 (周期 2 永不归零)
--------------------------------------------------------------------------------

-- +1 归零轨道: 0 → 1 → 2 → 0 → ... (三进制归零, SP2Ternary.succ3 的无限展开)
zero-reset-orbit : ℕ → Trit
zero-reset-orbit zero = T₀
zero-reset-orbit (suc zero) = T₁
zero-reset-orbit (suc (suc zero)) = T₂
zero-reset-orbit (suc (suc (suc t))) = zero-reset-orbit t

-- 3 的倍数步回归原点 (定义方程的归纳闭合)
threes : ℕ → ℕ
threes zero = zero
threes (suc k) = suc (suc (suc (threes k)))

zr-period3 : ∀ k → zero-reset-orbit (threes k) ≡ T₀
zr-period3 zero = refl
zr-period3 (suc k) = zr-period3 k

-- 闭合实例: 3 步/6 步归零
zr-closes-3 : zero-reset-orbit 3 ≡ T₀
zr-closes-3 = refl

zr-closes-6 : zero-reset-orbit 6 ≡ T₀
zr-closes-6 = refl

-- ×2 乌比斯环轨道: 1 ↔ 2, 永不经过 0 (SP2Ternary.double 的无限展开)
mobius-orbit : ℕ → Trit
mobius-orbit zero = T₁
mobius-orbit (suc zero) = T₂
mobius-orbit (suc (suc t)) = mobius-orbit t

twos : ℕ → ℕ
twos zero = zero
twos (suc k) = suc (suc (twos k))

-- 周期 2: 偶数步回到 1
mobius-period2 : ∀ k → mobius-orbit (twos k) ≡ T₁
mobius-period2 zero = refl
mobius-period2 (suc k) = mobius-period2 k

-- 永不归零: 卡在周期里出不去 (全 t 归纳)
mobius-never-zero : ∀ t → mobius-orbit t ≢ T₀
mobius-never-zero zero ()
mobius-never-zero (suc zero) ()
mobius-never-zero (suc (suc t)) = mobius-never-zero t

-- 两条轨道的区分: ×2 轨道任何时刻都不在 +1 轨道的归零点上
orbits-distinct : ∀ t → mobius-orbit t ≢ zero-reset-orbit (threes t)
orbits-distinct t eq = mobius-never-zero t (trans eq (zr-period3 t))

--------------------------------------------------------------------------------
-- §4. 卢先生阶数序列: 3,5,8,13,21,34,55,89,144
--   矢量方向计数的命名层序列; 斐波那契递推在证明层逐节锁定,
--   序列终点 144 = POLAR_WINDING (极向缠绕, 全息 π = 144/46 的分子)
--------------------------------------------------------------------------------

lu-orders : Vec ℕ 9
lu-orders = 3 ∷ 5 ∷ 8 ∷ 13 ∷ 21 ∷ 34 ∷ 55 ∷ 89 ∷ 144 ∷ []

lu-fib-1 : 3 + 5 ≡ 8
lu-fib-1 = refl

lu-fib-2 : 5 + 8 ≡ 13
lu-fib-2 = refl

lu-fib-3 : 8 + 13 ≡ 21
lu-fib-3 = refl

lu-fib-4 : 13 + 21 ≡ 34
lu-fib-4 = refl

lu-fib-5 : 21 + 34 ≡ 55
lu-fib-5 = refl

lu-fib-6 : 34 + 55 ≡ 89
lu-fib-6 = refl

lu-fib-7 : 55 + 89 ≡ 144
lu-fib-7 = refl

-- 框架常数锚定: 序列终点 = 极向缠绕 144
lu-144-polar : 144 ≡ POLAR_WINDING
lu-144-polar = refl

-- 0 postulate.
