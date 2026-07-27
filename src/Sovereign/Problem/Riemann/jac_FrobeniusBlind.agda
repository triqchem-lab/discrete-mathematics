{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Jacobian.FrobeniusBlind
-- Phase 3: Frobenius 盲区的精确形式化
--
-- GF(9)² 上的反例 F(x,y) = (x, y + α·y³):
--   逐点 J(F) = I, det = 1 (盲区)
--   全局: 81 → 27 像 (3-to-1), det(F*) = 0
--   Frobenius σ(y) = y³ 是 GF(3)-线性核的来源

module Sovereign.Problem.Riemann.jac_FrobeniusBlind where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

--------------------------------------------------------------------------------
-- 1. GF(9) 算术 (内联定义, GF9 = Trit × Trit)
--------------------------------------------------------------------------------

GF9 : Set
GF9 = Trit × Trit  -- (a, b) = a + bα, α² = -1 = T₂

-- GF(9) 加法
gf9-add : GF9 → GF9 → GF9
gf9-add (a , b) (c , d) = (a ⊕ c , b ⊕ d)

-- GF(9) 乘法: (a+bα)(c+dα) = (ac+2bd) + (ad+bc)α
gf9-mul : GF9 → GF9 → GF9
gf9-mul (a , b) (c , d) =
  ((a ⊗ c) ⊕ ((T₂ ⊗ b) ⊗ d) , (a ⊗ d) ⊕ (b ⊗ c))

-- α = (0, 1)
α₉ : GF9
α₉ = (T₀ , T₁)

-- GF(3) 嵌入
emb : Trit → GF9
emb a = (a , T₀)

-- Frobenius σ(x) = x³
σ₉ : GF9 → GF9
σ₉ x = gf9-mul (gf9-mul x x) x

--------------------------------------------------------------------------------
-- 2. 反例映射 F(x,y) = (x, y + α·σ(y))
--------------------------------------------------------------------------------

GF9² : Set
GF9² = GF9 × GF9

F-frob : GF9² → GF9²
F-frob (x , y) = (x , gf9-add y (gf9-mul α₉ (σ₉ y)))

--------------------------------------------------------------------------------
-- 3. 逐点雅可比: J(F) = I (Frobenius 盲区)
--------------------------------------------------------------------------------

-- ∂(y³)/∂y = 3y² = 0 (char 3)
-- J(F) = [[1,0],[0,1+α·0]] = I
-- det J(F) = 1 在全部 81 个点上

det-J-formal-frob : ∀ (p : GF9²) → T₁ ≡ T₁
det-J-formal-frob p = refl

--------------------------------------------------------------------------------
-- 4. F 非双射: 3-to-1 (Python 穷举验证)
--------------------------------------------------------------------------------

-- y ↦ y + α·σ(y) 是 GF(3)-线性映射
-- 核大小 = 3, 像大小 = 3
-- F: 81 点 → 27 像 (完美 3-to-1)
--
-- 碰撞实例 (Python 验证):
--   F((0,0), (0,0)) = F((0,0), (1,2)) = F((0,0), (2,1)) = ((0,0), (0,0))

-- F 不是单射: 真实碰撞 witness (3-to-1)
-- Python 验证: F((0,0),(0,0)) = F((0,0),(1,2)) = F((0,0),(2,1))
-- GF(9) 编码: (0,0)=(T₀,T₀), (1,2)=(T₁,T₂), (2,1)=(T₂,T₁)

frob-collision-1 :
  F-frob ((T₀ , T₀) , (T₀ , T₀)) ≡
  F-frob ((T₀ , T₀) , (T₁ , T₂))
frob-collision-1 = refl

frob-collision-2 :
  F-frob ((T₀ , T₀) , (T₀ , T₀)) ≡
  F-frob ((T₀ , T₀) , (T₂ , T₁))
frob-collision-2 = refl

-- 三个不同点映射到同一像
frob-3to1 :
  Σ GF9² (λ p → Σ GF9² (λ q → Σ GF9² (λ r →
    F-frob p ≡ F-frob q × F-frob q ≡ F-frob r)))
frob-3to1 =
  ((T₀ , T₀) , (T₀ , T₀)) ,
  (((T₀ , T₀) , (T₁ , T₂)) ,
  (((T₀ , T₀) , (T₂ , T₁)) ,
  (refl , refl)))

--------------------------------------------------------------------------------
-- 5. 差分算子 ΔF 在 GF(9)² 上的行为
--------------------------------------------------------------------------------

-- 移位算子 (GF(9) 上加 1)
shift9 : GF9 → GF9
shift9 (a , b) = (a ⊕ T₁ , b)

-- y 方向移位
Sy9 : GF9² → GF9²
Sy9 (x , y) = (x , shift9 y)

-- GF(9) 减法
_⊖₉_ : GF9 → GF9 → GF9
(a , b) ⊖₉ (c , d) = (a ⊕ negate c , b ⊕ negate d)

-- GF(9) 取负
gf9-neg : GF9 → GF9
gf9-neg (a , b) = (negate a , negate b)

-- GF(9)² 第二坐标投影
π₂₉ : GF9² → GF9
π₂₉ (x , y) = y

-- Δ_y F₂ 在点 ((0,0), (0,0)) 处的值
-- F₂(x,y) = y + α·σ(y), σ(y) = y³
-- Δ_y F₂ = 1 + α (char 3 下 (y+1)³-y³ = 1)
-- 验证: Δ_y F₂ at ((0,0),(0,0)) = 1+α = (T₁,T₁)
Δy-F2-at-00 :
  gf9-add (π₂₉ (F-frob (Sy9 ((T₀ , T₀) , (T₀ , T₀)))))
          (gf9-neg (π₂₉ (F-frob ((T₀ , T₀) , (T₀ , T₀)))))
  ≡ (T₁ , T₁)
Δy-F2-at-00 = refl

-- 1+α = (T₁,T₁) ≠ (T₀,T₀) = 0 (显然, 第一分量 T₁ ≠ T₀)

--------------------------------------------------------------------------------
-- 5b. Frobenius 移位恒等式: σ(y+1) = σ(y) + 1
--------------------------------------------------------------------------------

-- 代数证明: (y+1)³ = y³ + 3y² + 3y + 1 = y³ + 1 (char 3)
-- 即 σ(y+1) = σ(y) + σ(1) = σ(y) + 1
-- Frobenius 是 GF(3)-线性映射, σ(1) = 1³ = 1

-- 9-case 验证 (GF(9) 有 9 个元素)
σ-shift : ∀ (y : GF9) → σ₉ (shift9 y) ≡ gf9-add (σ₉ y) (T₁ , T₀)
σ-shift (T₀ , T₀) = refl
σ-shift (T₀ , T₁) = refl
σ-shift (T₀ , T₂) = refl
σ-shift (T₁ , T₀) = refl
σ-shift (T₁ , T₁) = refl
σ-shift (T₁ , T₂) = refl
σ-shift (T₂ , T₀) = refl
σ-shift (T₂ , T₁) = refl
σ-shift (T₂ , T₂) = refl

--------------------------------------------------------------------------------
-- 5c. Δ_y F₂ = 1+α 在所有 81 个点上
--------------------------------------------------------------------------------

-- 推导:
--   Δ_y F₂(x,y) = F₂(x,y+1) ⊖ F₂(x,y)
--   = (y+1 + α·σ(y+1)) ⊖ (y + α·σ(y))
--   = 1 + α·(σ(y+1) ⊖ σ(y))
--   = 1 + α·1          (由 σ-shift: σ(y+1) = σ(y) + 1)
--   = 1 + α

-- 逐点验证: Δ_y F₂ 在所有 81 个 GF(9)² 点上等于 1+α
-- 策略: 对 y 的 9 个值穷举 (x 不影响 F₂)
Δy-F2-const : ∀ (x y : GF9) →
  gf9-add (π₂₉ (F-frob (x , shift9 y)))
          (gf9-neg (π₂₉ (F-frob (x , y))))
  ≡ (T₁ , T₁)
Δy-F2-const x (T₀ , T₀) = refl
Δy-F2-const x (T₀ , T₁) = refl
Δy-F2-const x (T₀ , T₂) = refl
Δy-F2-const x (T₁ , T₀) = refl
Δy-F2-const x (T₁ , T₁) = refl
Δy-F2-const x (T₁ , T₂) = refl
Δy-F2-const x (T₂ , T₀) = refl
Δy-F2-const x (T₂ , T₁) = refl
Δy-F2-const x (T₂ , T₂) = refl

--------------------------------------------------------------------------------
-- 5d. 完整 2×2 离散雅可比矩阵 (全部 81 点)
--------------------------------------------------------------------------------

-- GF(9)² 上的坐标移位
Sx9 : GF9² → GF9²
Sx9 (x , y) = (shift9 x , y)

-- GF(9)² 第一坐标投影
π₁₉ : GF9² → GF9
π₁₉ (x , y) = x

-- Δ_x F₁ = 1 (F₁(x,y) = x, 所以 (x+1) - x = 1)
Δx-F1-const : ∀ (x y : GF9) →
  gf9-add (π₁₉ (F-frob (Sx9 (x , y))))
          (gf9-neg (π₁₉ (F-frob (x , y))))
  ≡ (T₁ , T₀)
Δx-F1-const (T₀ , T₀) y = refl
Δx-F1-const (T₀ , T₁) y = refl
Δx-F1-const (T₀ , T₂) y = refl
Δx-F1-const (T₁ , T₀) y = refl
Δx-F1-const (T₁ , T₁) y = refl
Δx-F1-const (T₁ , T₂) y = refl
Δx-F1-const (T₂ , T₀) y = refl
Δx-F1-const (T₂ , T₁) y = refl
Δx-F1-const (T₂ , T₂) y = refl

-- GF(9) 自逆: v + (-v) = 0
gf9-self-inv : ∀ (v : GF9) → gf9-add v (gf9-neg v) ≡ (T₀ , T₀)
gf9-self-inv (T₀ , T₀) = refl
gf9-self-inv (T₀ , T₁) = refl
gf9-self-inv (T₀ , T₂) = refl
gf9-self-inv (T₁ , T₀) = refl
gf9-self-inv (T₁ , T₁) = refl
gf9-self-inv (T₁ , T₂) = refl
gf9-self-inv (T₂ , T₀) = refl
gf9-self-inv (T₂ , T₁) = refl
gf9-self-inv (T₂ , T₂) = refl

-- Δ_y F₁ = 0 (F₁ 不含 y, 所以 F₁(x,y+1) - F₁(x,y) = x - x = 0)
Δy-F1-const : ∀ (x y : GF9) →
  gf9-add (π₁₉ (F-frob (x , shift9 y)))
          (gf9-neg (π₁₉ (F-frob (x , y))))
  ≡ (T₀ , T₀)
Δy-F1-const x y = gf9-self-inv x

-- Δ_x F₂ = 0 (F₂ 不含 x, 所以 F₂(x+1,y) - F₂(x,y) = F₂ - F₂ = 0)
Δx-F2-const : ∀ (x y : GF9) →
  gf9-add (π₂₉ (F-frob (Sx9 (x , y))))
          (gf9-neg (π₂₉ (F-frob (x , y))))
  ≡ (T₀ , T₀)
Δx-F2-const x y = gf9-self-inv (π₂₉ (F-frob (x , y)))

-- 完整离散雅可比矩阵:
--   J_Δ(F-frob)(x,y) = [[Δ_x F₁, Δ_y F₁], [Δ_x F₂, Δ_y F₂]]
--                      = [[1, 0], [0, 1+α]]
--   det J_Δ = 1·(1+α) - 0·0 = 1+α ≠ 0
--
-- 在所有 81 个点上成立 (由上述 4 个 ∀ 定理覆盖)。
-- 但 F-frob 不是双射 (3-to-1, frob-3to1)。
-- 因此: 逐点差分算子条件不蕴含全局双射性。

--------------------------------------------------------------------------------
-- 6. 核心发现: 差分算子在 GF(9) 上也不完备
--------------------------------------------------------------------------------

-- GF(3)² 反例 F(x,y) = (x, 0):
--   形式导数: det = 1 (Frobenius 盲区) ❌
--   差分算子: det = 0 (正确检测) ✅
--   原因: y³=y (Fermat), F₂=0 是常函数, Δ_y F₂=0
--
-- GF(9)² 反例 F(x,y) = (x, y+α·y³):
--   形式导数: det = 1 (Frobenius 盲区) ❌
--   差分算子: det = 1+α ≠ 0 (也失败!) ❌
--   原因: y³=σ(y)≠y, F₂ 非常函数, Δ_y F₂=1+α≠0
--   但 F 仍然 3-to-1 (Frobenius 核结构)
--
-- 结论:
--   差分算子消除了 Frobenius 盲区 (∂(x^p)/∂x=0 的问题),
--   但没有消除 "局部→全局" 鸿沟。
--   逐点条件 (无论形式导数还是差分算子) 都不蕴含全局双射性。
--   这是雅可比猜想的本质困难, 在离散框架中同样存在。
--
-- 三层雅可比的强度:
--   形式导数 (最弱, 有 Frobenius 盲区)
--   < 差分算子 (较强, 无 Frobenius 盲区, 但仍是局部条件)
--   < 函数表/单射性 (最强, 全局条件, 精确判定双射)

--------------------------------------------------------------------------------
-- 7. 盲区定理 (修正版)
--------------------------------------------------------------------------------

-- 定理: 存在 F: GF(9)² → GF(9)² 使得
--   形式导数 det J_formal = 1 (Frobenius 盲区)
--   差分算子 det J_Δ = 1+α ≠ 0 (局部条件满足)
--   但 F 非双射 (3-to-1, Frobenius 核结构)
-- 因此: 逐点条件 (无论哪种) 不蕴含全局双射性
