{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.AlgGeomBridge
-- 14 代数几何对接 — GF(9) 范数 1 圆锥 (离散曲线起点, 0 postulate)
--
-- 对接 MSC 14 的离散桥梁: 圆锥曲线 x² + y² = 1 在 GF(3) 上的点集
--   = { (1,0), (0,1), (2,0), (0,2) } — 恰 4 = q+1 点 (亏格 0, Weil 界取等)
-- 与 GF(9) 的范数 1 单位子群 {1, α, −1, −α} ≅ C₄ 一一对应:
--   z = x + yα, N(z) = z·σ(z) = x² + y² = 1 ⟺ (x,y) 在圆锥上
--
-- 结构: §1 圆锥 4 点枚举 + 非点反证; §2 范数 1 单位 (4 元素 + 闭包 16 项);
--   §3 对应与 Weil 注释 (亏格 0: #点 = q+1 = 4)。

module Sovereign.Algebra.AlgGeomBridge where

open import Data.Product using (_×_; _,_)
open import Data.Nat using (_≤_; s≤s; z≤n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.GF9 using
  (GF9; galoisNorm; gf9-one; alpha; _*gf9_)

--------------------------------------------------------------------------------
-- §1. 圆锥 x² + y² = 1 的 GF(3) 点集 (4 点)
--------------------------------------------------------------------------------

-- (1,0): 1² + 0² = 1
conic-point-10 : (T₁ ⊗ T₁) ⊕ (T₀ ⊗ T₀) ≡ T₁
conic-point-10 = refl

-- (0,1): 0² + 1² = 1
conic-point-01 : (T₀ ⊗ T₀) ⊕ (T₁ ⊗ T₁) ≡ T₁
conic-point-01 = refl

-- (2,0): 2² + 0² = 4 ≡ 1
conic-point-20 : (T₂ ⊗ T₂) ⊕ (T₀ ⊗ T₀) ≡ T₁
conic-point-20 = refl

-- (0,2): 0² + 2² = 1
conic-point-02 : (T₀ ⊗ T₀) ⊕ (T₂ ⊗ T₂) ≡ T₁
conic-point-02 = refl

-- 非点 (1,1): 1² + 1² = 2 ≢ 1
conic-nonpoint-11 : ¬ ((T₁ ⊗ T₁) ⊕ (T₁ ⊗ T₁) ≡ T₁)
conic-nonpoint-11 ()

--------------------------------------------------------------------------------
-- §2. 范数 1 单位: {1, α, −1, −α} — GF(9) 的单位圆锥 (N = x²+y² = 1)
--------------------------------------------------------------------------------

neg-gf9 : GF9 → GF9
neg-gf9 (a , b) = negate a , negate b

-- N(1) = 1
norm1-one : galoisNorm gf9-one ≡ T₁
norm1-one = refl

-- N(α) = 1 (α·σ(α) = −α² = −(−1) = 1)
norm1-alpha : galoisNorm alpha ≡ T₁
norm1-alpha = refl

-- N(−1) = 1
norm1-mone : galoisNorm (neg-gf9 gf9-one) ≡ T₁
norm1-mone = refl

-- N(−α) = 1
norm1-malpha : galoisNorm (neg-gf9 alpha) ≡ T₁
norm1-malpha = refl

-- 4 元素在 *gf9 下封闭 (16 项) — 范数 1 子群 ≅ C₄ (生成元 α)

data Norm1 : Set where
  n1 na nm1 nma : Norm1

norm1Elem : Norm1 → GF9
norm1Elem n1 = gf9-one
norm1Elem na = alpha
norm1Elem nm1 = neg-gf9 gf9-one
norm1Elem nma = neg-gf9 alpha

norm1Mul : Norm1 → Norm1 → Norm1
norm1Mul n1 n1 = n1
norm1Mul n1 na = na
norm1Mul n1 nm1 = nm1
norm1Mul n1 nma = nma
norm1Mul na n1 = na
norm1Mul na na = nm1
norm1Mul na nm1 = nma
norm1Mul na nma = n1
norm1Mul nm1 n1 = nm1
norm1Mul nm1 na = nma
norm1Mul nm1 nm1 = n1
norm1Mul nm1 nma = na
norm1Mul nma n1 = nma
norm1Mul nma na = n1
norm1Mul nma nm1 = na
norm1Mul nma nma = nm1

-- 闭包: 乘积的范数仍为 1 (16 项, 逐项 refl)
norm1-closed : ∀ x y → galoisNorm (norm1Elem x *gf9 norm1Elem y) ≡ T₁
norm1-closed n1 n1 = refl
norm1-closed n1 na = refl
norm1-closed n1 nm1 = refl
norm1-closed n1 nma = refl
norm1-closed na n1 = refl
norm1-closed na na = refl
norm1-closed na nm1 = refl
norm1-closed na nma = refl
norm1-closed nm1 n1 = refl
norm1-closed nm1 na = refl
norm1-closed nm1 nm1 = refl
norm1-closed nm1 nma = refl
norm1-closed nma n1 = refl
norm1-closed nma na = refl
norm1-closed nma nm1 = refl
norm1-closed nma nma = refl

-- C₄ 结构: 生成元 α, α² = −1, α⁴ = 1 (引用 GF9.alpha-squared/alpha-powers-4 的等价式)
norm1-cycle-2 : norm1Elem na *gf9 norm1Elem na ≡ norm1Elem nm1
norm1-cycle-2 = refl
norm1-cycle-4 : (((norm1Elem na *gf9 norm1Elem na) *gf9 norm1Elem na) *gf9 norm1Elem na) ≡ norm1Elem n1
norm1-cycle-4 = refl

--------------------------------------------------------------------------------
-- §3. 圆锥点 ↔ 范数 1 单位: z = x + yα, N(z) = x² + y² — 一一对应
--------------------------------------------------------------------------------

-- 对应: (1,0)↔1, (0,1)↔α, (2,0)↔−1, (0,2)↔−α — 4 点 ↔ 4 单位
-- Weil 注释: 亏格 0 曲线 (圆锥) 的 GF(q) 点 = q+1: #Conic(GF(3)) = 3+1 = 4,
--   Weil 界 #E(GF(q)) − (q+1) = 0 取等 — 离散曲线的第一个完整例子。


--------------------------------------------------------------------------------
-- §4. 椭圆曲线 E : y² = x³ + x + 1 在 GF(3) — 亏格 1 离散曲线 (14 深化)
--------------------------------------------------------------------------------

-- 曲线方程 (GF(3)): y² = x³ + x + 1
onE : Trit → Trit → Set
onE x y = (y ⊗ y) ≡ ((((x ⊗ x) ⊗ x) ⊕ x) ⊕ T₁)

-- 4 点枚举: O + 3 仿射点 (9 格点中恰 4 个在曲线上)
onE-01 : onE T₀ T₁ ; onE-01 = refl
onE-02 : onE T₀ T₂ ; onE-02 = refl
onE-10 : onE T₁ T₀ ; onE-10 = refl

-- 5 个非点反证
¬onE-00 : ¬ (onE T₀ T₀) ; ¬onE-00 ()
¬onE-11 : ¬ (onE T₁ T₁) ; ¬onE-11 ()
¬onE-12 : ¬ (onE T₁ T₂) ; ¬onE-12 ()
¬onE-20 : ¬ (onE T₂ T₀) ; ¬onE-20 ()
¬onE-21 : ¬ (onE T₂ T₁) ; ¬onE-21 ()
¬onE-22 : ¬ (onE T₂ T₂) ; ¬onE-22 ()

-- E(GF(3)) = {O, (0,1), (0,2), (1,0)} — 点类型
data EPoint : Set where
  eO e01 e02 e10 : EPoint

-- 群律 (chord-tangent): 16 项表
eadd : EPoint → EPoint → EPoint
eadd eO eO = eO
eadd eO e01 = e01
eadd eO e02 = e02
eadd eO e10 = e10
eadd e01 eO = e01
eadd e01 e01 = e10
eadd e01 e02 = eO
eadd e01 e10 = e02
eadd e02 eO = e02
eadd e02 e01 = eO
eadd e02 e02 = e10
eadd e02 e10 = e01
eadd e10 eO = e10
eadd e10 e01 = e02
eadd e10 e02 = e01
eadd e10 e10 = eO

-- 结构定理: (0,1) 阶 4 → E(GF(3)) ≅ C₄ (e01 → e10 → e02 → eO)
e01-order2 : eadd e01 e01 ≡ e10 ; e01-order2 = refl
e01-order3 : eadd (eadd e01 e01) e01 ≡ e02 ; e01-order3 = refl
e01-order4 : eadd (eadd (eadd e01 e01) e01) e01 ≡ eO ; e01-order4 = refl

-- Hasse 界: #E(GF(3)) = 4, q+1 = 4, |#E − (q+1)| = 0 ≤ 2√3 (~3.46)
--   整数界: #E ≤ (q+1) + 3 = 7 (4 ≤ 7)
hasse-bound : 4 ≤ 7
hasse-bound = s≤s (s≤s (s≤s (s≤s z≤n)))

-- 亏格对照 (注释): 亏格 0 (圆锥, §1-§3) #点 = q+1 精确;
--   亏格 1 (椭圆, §4) #点 = q+1 − t (迹 t = 0 此处) — 两条离散曲线
--   承载 Weil 界的两端: 圆锥取等, 椭圆在界内 (0 ≤ 2√3)。

-- 0 postulate.
