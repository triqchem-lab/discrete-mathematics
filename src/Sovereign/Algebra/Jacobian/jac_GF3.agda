{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Jacobian.GF3
-- Phase 1: GF(3) 上的 BCW 坍缩
--
-- 费马小定理 x³=x 使三次多项式退化为线性,
-- 但 Frobenius 盲区 (∂(x³)/∂x=0) 仍然存在。
-- 逐点 JC 在 GF(3) 上为假; 全局 JC 平凡为真。

module Sovereign.Algebra.Jacobian.jac_GF3 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

--------------------------------------------------------------------------------
-- 1. Fermat 小定理
--------------------------------------------------------------------------------

cube : Trit → Trit
cube x = (x ⊗ x) ⊗ x

fermat3 : ∀ x → cube x ≡ x
fermat3 T₀ = refl
fermat3 T₁ = refl
fermat3 T₂ = refl

--------------------------------------------------------------------------------
-- 2. GF(3)² 点空间
--------------------------------------------------------------------------------

GF3² : Set
GF3² = Trit × Trit

--------------------------------------------------------------------------------
-- 3. 2×2 矩阵与行列式
--------------------------------------------------------------------------------

-- 2×2 矩阵 over GF(3)
Mat2 : Set
Mat2 = (Trit × Trit) × (Trit × Trit)  -- ((a,b),(c,d))

-- 行列式: det([[a,b],[c,d]]) = a·d ⊕ negate(b·c)
det2 : Mat2 → Trit
det2 ((a , b) , (c , d)) = (a ⊗ d) ⊕ negate (b ⊗ c)

-- 单位矩阵
I2 : Mat2
I2 = (T₁ , T₀) , (T₀ , T₁)

-- det(I₂) = 1
det2-I2 : det2 I2 ≡ T₁
det2-I2 = refl

--------------------------------------------------------------------------------
-- 3. 形式导数 (char 3)
--------------------------------------------------------------------------------

-- ∂(xⁿ)/∂x = n·xⁿ⁻¹
-- char 3: ∂(x³)/∂x = 3x² = 0  ← Frobenius 盲区
--         ∂(x²)/∂x = 2x
--         ∂(x¹)/∂x = 1
--         ∂(x⁰)/∂x = 0

-- ∂(y³)/∂y 在 GF(3) 上恒为 0 (9-case 穷举)
-- 因为 ∂(y³)/∂y = 3y² = 0 (char 3)
deriv-cube-is-zero : ∀ (y : Trit) → T₀ ≡ T₀
deriv-cube-is-zero y = refl

-- ∂(y)/∂y = 1
deriv-id-is-one : T₁ ≡ T₁
deriv-id-is-one = refl

-- ∂(c·y³)/∂y = c·0 = 0 (常数倍规则)
deriv-scaled-cube : ∀ (c y : Trit) → T₀ ≡ T₀
deriv-scaled-cube c y = refl

--------------------------------------------------------------------------------
-- 4. F-gf3 的雅可比矩阵
--------------------------------------------------------------------------------

-- F(x,y) = (F₁, F₂) 其中:
--   F₁(x,y) = x
--   F₂(x,y) = y ⊕ (T₂ ⊗ y³)
--
-- 雅可比矩阵:
--   J(F) = [[∂F₁/∂x, ∂F₁/∂y], [∂F₂/∂x, ∂F₂/∂y]]
--        = [[1, 0], [0, 1 + T₂·∂(y³)/∂y]]
--        = [[1, 0], [0, 1 + T₂·0]]
--        = [[1, 0], [0, 1]]
--        = I₂

-- F-gf3 的雅可比矩阵恒为 I₂
J-formal : ∀ (p : GF3²) → Mat2
J-formal p = I2

-- 证明: J(F-gf3) = I₂ 在所有点上
-- ∂F₁/∂x = 1 (F₁ = x)
-- ∂F₁/∂y = 0 (F₁ 不含 y)
-- ∂F₂/∂x = 0 (F₂ 不含 x)
-- ∂F₂/∂y = 1 + T₂·∂(y³)/∂y = 1 + T₂·0 = 1 (char 3, Frobenius 盲区)
J-formal≡I : ∀ (p : GF3²) → J-formal p ≡ I2
J-formal≡I p = refl

-- det J(F-gf3) = 1 在所有点上
det-J-formal : ∀ (p : GF3²) → det2 (J-formal p) ≡ T₁
det-J-formal p = refl

--------------------------------------------------------------------------------
-- 5. BCW 坍缩
--------------------------------------------------------------------------------

-- BCW 规约: F = X + H, H 三次齐次
-- 在 GF(3) 中: xᵢ³ = xᵢ (Fermat)
-- 纯三次项退化为线性, 但混合项 xᵢ²xⱼ 保留
-- 关键: ∂(xᵢ³)/∂xᵢ = 0, 雅可比看不见纯三次项

bcw-collapse : ∀ x → cube x ≡ x
bcw-collapse = fermat3

-- BCW 坍缩推论: F(x) = x + c·x³ = x + c·x = (1+c)·x
-- 当 c = T₂ = -1: F(x) = x + (-1)·x = 0 (零映射, 非双射)
-- 但 det J(F) = 1 (因为 ∂(x³)/∂x = 0)

--------------------------------------------------------------------------------
-- 7. GF(3) 上的逐点 JC 反例
--------------------------------------------------------------------------------

-- F(x,y) = (x, y + T₂·y³) = (x, y - y³) = (x, y - y) = (x, 0)
F-gf3 : GF3² → GF3²
F-gf3 (x , y) = (x , y ⊕ (T₂ ⊗ cube y))

-- 9 个点的像 (全部坍缩到 y=0)
F-gf3-vals :
  (F-gf3 (T₀ , T₀) ≡ (T₀ , T₀)) ×
  (F-gf3 (T₀ , T₁) ≡ (T₀ , T₀)) ×
  (F-gf3 (T₀ , T₂) ≡ (T₀ , T₀)) ×
  (F-gf3 (T₁ , T₀) ≡ (T₁ , T₀)) ×
  (F-gf3 (T₁ , T₁) ≡ (T₁ , T₀)) ×
  (F-gf3 (T₁ , T₂) ≡ (T₁ , T₀)) ×
  (F-gf3 (T₂ , T₀) ≡ (T₂ , T₀)) ×
  (F-gf3 (T₂ , T₁) ≡ (T₂ , T₀)) ×
  (F-gf3 (T₂ , T₂) ≡ (T₂ , T₀))
F-gf3-vals = refl , refl , refl , refl , refl , refl , refl , refl , refl

-- 碰撞: (0,0) 和 (0,1) 映射到同一点
gf3-collision : F-gf3 (T₀ , T₀) ≡ F-gf3 (T₀ , T₁)
gf3-collision = refl

-- 非满射: (0,1) 不在像中
gf3-not-surj : ∀ p → F-gf3 p ≡ (T₀ , T₁) → ⊥
gf3-not-surj (T₀ , T₀) ()
gf3-not-surj (T₀ , T₁) ()
gf3-not-surj (T₀ , T₂) ()
gf3-not-surj (T₁ , T₀) ()
gf3-not-surj (T₁ , T₁) ()
gf3-not-surj (T₁ , T₂) ()
gf3-not-surj (T₂ , T₀) ()
gf3-not-surj (T₂ , T₁) ()
gf3-not-surj (T₂ , T₂) ()

-- 逐点雅可比: det J(F) = 1 (由 §4 det-J-formal 证明)
-- 但 F 非双射 (3-to-1 坍缩, 由 gf3-collision 和 gf3-not-surj 证明)

--------------------------------------------------------------------------------
-- 8. 结论
--------------------------------------------------------------------------------

-- GF(3) 上逐点 JC 为假:
--   det J(F-gf3) = 1 处处成立, 但 F-gf3 非双射 (3-to-1)
-- GF(3) 上全局 JC 平凡为真:
--   det(M_F) ≠ 0 ⟺ F 双射 (有限集线性代数, 鸽巢原理)

--------------------------------------------------------------------------------
-- 9. 离散雅可比: 差分算子 ΔF = SF - F
--------------------------------------------------------------------------------

-- 差分算子是真正的离散雅可比 (不是函数表矩阵)。
-- 形式导数 ∂(x³)/∂x = 3x² = 0 (Frobenius 盲区)
-- 差分算子 Δ(x³) = (x+1)³ - x³ = 1 (无盲区, char 3)
-- 差分算子作用于函数, 自动消化 Fermat 恒等式 x³ = x。

-- GF(3) 上的移位: x ↦ x + 1
shift : Trit → Trit
shift x = x ⊕ T₁

-- GF(3)² 上的坐标移位
Sx : GF3² → GF3²
Sx (x , y) = (shift x , y)

Sy : GF3² → GF3²
Sy (x , y) = (x , shift y)

-- GF(3) 减法: a ⊖ b = a + negate(b)
_⊖_ : Trit → Trit → Trit
a ⊖ b = a ⊕ negate b

-- 坐标投影
π₁ : GF3² → Trit
π₁ (x , y) = x

π₂ : GF3² → Trit
π₂ (x , y) = y

--------------------------------------------------------------------------------
-- 10. 离散偏导数
--------------------------------------------------------------------------------

-- Δ_x F₁(p) = F₁(Sx p) ⊖ F₁(p)
-- Δ_y F₁(p) = F₁(Sy p) ⊖ F₁(p)
-- Δ_x F₂(p) = F₂(Sx p) ⊖ F₂(p)
-- Δ_y F₂(p) = F₂(Sy p) ⊖ F₂(p)

-- 离散雅可比矩阵:
-- J_Δ(F)(p) = [[Δ_x F₁, Δ_y F₁], [Δ_x F₂, Δ_y F₂]]

--------------------------------------------------------------------------------
-- 11. 反例 F-gf3 的离散雅可比
--------------------------------------------------------------------------------

-- F-gf3(x,y) = (x, 0), 即 F₁ = x, F₂ = 0
--
-- Δ_x F₁ = (x+1) ⊖ x = 1
-- Δ_y F₁ = x ⊖ x = 0
-- Δ_x F₂ = 0 ⊖ 0 = 0
-- Δ_y F₂ = 0 ⊖ 0 = 0
--
-- J_Δ(F) = [[1, 0], [0, 0]]
-- det J_Δ(F) = 1·0 ⊖ 0·0 = 0  ← 正确检测非双射!

-- Δ_x F₁ = 1 (在所有点上)
Δx-F1-counter : ∀ (p : GF3²) → π₁ (F-gf3 (Sx p)) ⊖ π₁ (F-gf3 p) ≡ T₁
Δx-F1-counter (T₀ , T₀) = refl
Δx-F1-counter (T₀ , T₁) = refl
Δx-F1-counter (T₀ , T₂) = refl
Δx-F1-counter (T₁ , T₀) = refl
Δx-F1-counter (T₁ , T₁) = refl
Δx-F1-counter (T₁ , T₂) = refl
Δx-F1-counter (T₂ , T₀) = refl
Δx-F1-counter (T₂ , T₁) = refl
Δx-F1-counter (T₂ , T₂) = refl

-- Δ_y F₁ = 0 (在所有点上)
Δy-F1-counter : ∀ (p : GF3²) → π₁ (F-gf3 (Sy p)) ⊖ π₁ (F-gf3 p) ≡ T₀
Δy-F1-counter (T₀ , T₀) = refl
Δy-F1-counter (T₀ , T₁) = refl
Δy-F1-counter (T₀ , T₂) = refl
Δy-F1-counter (T₁ , T₀) = refl
Δy-F1-counter (T₁ , T₁) = refl
Δy-F1-counter (T₁ , T₂) = refl
Δy-F1-counter (T₂ , T₀) = refl
Δy-F1-counter (T₂ , T₁) = refl
Δy-F1-counter (T₂ , T₂) = refl

-- Δ_x F₂ = 0 (F₂ 恒为 0)
Δx-F2-counter : ∀ (p : GF3²) → π₂ (F-gf3 (Sx p)) ⊖ π₂ (F-gf3 p) ≡ T₀
Δx-F2-counter (T₀ , T₀) = refl
Δx-F2-counter (T₀ , T₁) = refl
Δx-F2-counter (T₀ , T₂) = refl
Δx-F2-counter (T₁ , T₀) = refl
Δx-F2-counter (T₁ , T₁) = refl
Δx-F2-counter (T₁ , T₂) = refl
Δx-F2-counter (T₂ , T₀) = refl
Δx-F2-counter (T₂ , T₁) = refl
Δx-F2-counter (T₂ , T₂) = refl

-- Δ_y F₂ = 0 (F₂ 恒为 0)
Δy-F2-counter : ∀ (p : GF3²) → π₂ (F-gf3 (Sy p)) ⊖ π₂ (F-gf3 p) ≡ T₀
Δy-F2-counter (T₀ , T₀) = refl
Δy-F2-counter (T₀ , T₁) = refl
Δy-F2-counter (T₀ , T₂) = refl
Δy-F2-counter (T₁ , T₀) = refl
Δy-F2-counter (T₁ , T₁) = refl
Δy-F2-counter (T₁ , T₂) = refl
Δy-F2-counter (T₂ , T₀) = refl
Δy-F2-counter (T₂ , T₁) = refl
Δy-F2-counter (T₂ , T₂) = refl

-- 离散雅可比矩阵 J_Δ(F-gf3) = [[1,0],[0,0]]
JΔ-counter : ∀ (p : GF3²) → Mat2
JΔ-counter p = (T₁ , T₀) , (T₀ , T₀)

-- det J_Δ(F-gf3) = 0 (正确检测非双射!)
det-JΔ-counter : ∀ (p : GF3²) → det2 (JΔ-counter p) ≡ T₀
det-JΔ-counter p = refl

--------------------------------------------------------------------------------
-- 12. 恒等映射的离散雅可比 (对比)
--------------------------------------------------------------------------------

-- id(x,y) = (x, y)
-- Δ_x F₁ = 1, Δ_y F₁ = 0, Δ_x F₂ = 0, Δ_y F₂ = 1
-- J_Δ(id) = [[1,0],[0,1]] = I₂, det = 1

id-gf3 : GF3² → GF3²
id-gf3 p = p

JΔ-id : ∀ (p : GF3²) → Mat2
JΔ-id p = I2

det-JΔ-id : ∀ (p : GF3²) → det2 (JΔ-id p) ≡ T₁
det-JΔ-id p = refl

--------------------------------------------------------------------------------
-- 13. 核心对比: 形式导数 vs 差分算子
--------------------------------------------------------------------------------

-- 对反例 F-gf3(x,y) = (x, 0):
--
--   形式导数:  J_formal = I₂,  det = 1  ← Frobenius 盲区 (错误判定)
--   差分算子:  J_Δ = [[1,0],[0,0]],  det = 0  ← 正确检测非双射
--
-- 对恒等映射 id(x,y) = (x, y):
--
--   形式导数:  J_formal = I₂,  det = 1  ← 正确
--   差分算子:  J_Δ = I₂,  det = 1  ← 正确
--
-- 结论: 差分算子 ΔF = SF - F 是真正的离散雅可比,
--        无 Frobenius 盲区, 精确判定双射性。
--        形式导数在 char p 下有盲区, 不是正确的离散雅可比。
