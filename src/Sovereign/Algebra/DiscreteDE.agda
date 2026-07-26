{-# OPTIONS --rewriting #-}
module Sovereign.Algebra.DiscreteDE where

--------------------------------------------------------------------------------
-- 离散微分方程 — ODE/PDE 的 GF(3) 离散替代
--
-- MSC 34-35: 离散 ODE/PDE 的 GF(3) 本体
--
-- 核心原则:
--   连续 ODE dy/dx = f(x,y) 是离散 ODE Δy(x) = f(x, y(x)) 的"不存在的极限"
--   步长 h = 1 固定 (T₁ ≢ T₀), 极限 h→0 在 GF(3) 中不存在
--   Δ³ ≡ 0 (幂零性) 使得所有 ≥3 阶离散 ODE 的最高阶导数恒为零
--
-- 内容:
--   §1. GF(3) 辅助引理 (消去律)
--   §2. 高阶差分算子 Δⁿ 与幂零性推广
--   §3. GF3Func 求值与制表
--   §4. 线性离散 ODE: Δy = g (Fredholm 相容性 + 解的构造)
--   §5. 非线性离散 ODE: Δy(x) = f(x, y(x))
--   §6. 二维离散 PDE: 离散 Laplace 方程 Δ₁²u + Δ₂²u = 0
--   §7. 幂零性推论: ≥3 阶 ODE 的最高阶导数恒为零
--   §8. 与连续 DE 的投影关系
--
-- 依赖:
--   ProjectionDifferential: Δ³≡0, Δ²-is-const, shift³≡id, sum3-Δ≡0
--   Trit: GF(3) 代数
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (
  _≡_; _≢_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; negate²;
  ⊕-identityˡ; ⊕-identityʳ; ⊕-comm; ⊕-assoc; ⊕-inverse)
open import Sovereign.Algebra.ProjectionDifferential using (
  GF3Func; shift; Δ; sum3; const-func; eval₀;
  Δ³≡0; Δ²-is-const; Δ-const-zero; shift³≡id; sum3-Δ≡0; step-nonzero)

--------------------------------------------------------------------------------
-- §1. GF(3) 辅助引理
--
-- 离散 ODE 的解的构造和验证需要 GF(3) 的消去律。
-- 全部 9 case 穷举 (GF(3) 算术归约)。
--------------------------------------------------------------------------------

-- 左消去: (a + b) + (-a) = b
-- 代数本质: 加法群中的消去律
⊕-cancelˡ : ∀ a b → (a ⊕ b) ⊕ negate a ≡ b
⊕-cancelˡ T₀ T₀ = refl
⊕-cancelˡ T₀ T₁ = refl
⊕-cancelˡ T₀ T₂ = refl
⊕-cancelˡ T₁ T₀ = refl
⊕-cancelˡ T₁ T₁ = refl
⊕-cancelˡ T₁ T₂ = refl
⊕-cancelˡ T₂ T₀ = refl
⊕-cancelˡ T₂ T₁ = refl
⊕-cancelˡ T₂ T₂ = refl

-- 右消去: x + y = 0 → y = -x
-- 代数本质: 加法逆元的唯一性
⊕-right-cancel : ∀ x y → x ⊕ y ≡ T₀ → y ≡ negate x
⊕-right-cancel T₀ T₀ _ = refl
⊕-right-cancel T₀ T₁ ()
⊕-right-cancel T₀ T₂ ()
⊕-right-cancel T₁ T₀ ()
⊕-right-cancel T₁ T₁ ()
⊕-right-cancel T₁ T₂ _ = refl
⊕-right-cancel T₂ T₀ ()
⊕-right-cancel T₂ T₁ _ = refl
⊕-right-cancel T₂ T₂ ()

-- 差为零则相等: x + (-y) = 0 → x = y
-- 代数本质: 加法群的 Hausdorff 性质
⊕-negate≡0→≡ : ∀ x y → x ⊕ negate y ≡ T₀ → x ≡ y
⊕-negate≡0→≡ T₀ T₀ _ = refl
⊕-negate≡0→≡ T₀ T₁ ()
⊕-negate≡0→≡ T₀ T₂ ()
⊕-negate≡0→≡ T₁ T₀ ()
⊕-negate≡0→≡ T₁ T₁ _ = refl
⊕-negate≡0→≡ T₁ T₂ ()
⊕-negate≡0→≡ T₂ T₀ ()
⊕-negate≡0→≡ T₂ T₁ ()
⊕-negate≡0→≡ T₂ T₂ _ = refl

-- 三元组等式: 逐分量构造
triple-≡ : ∀ {a b c a' b' c' : Trit} →
  a ≡ a' → b ≡ b' → c ≡ c' → (a , b , c) ≡ (a' , b' , c')
triple-≡ refl refl refl = refl

-- 三元组等式分解: 提取各分量
triple-decomp : ∀ {a b c : Trit} →
  (a , b , c) ≡ (T₀ , T₀ , T₀) → a ≡ T₀ × b ≡ T₀ × c ≡ T₀
triple-decomp refl = refl , (refl , refl)

--------------------------------------------------------------------------------
-- §2. 高阶差分算子 Δⁿ — 幂零性推广
--
-- Δ⁰ = id, Δ¹ = Δ, Δ² = Δ∘Δ, Δ³ = 0 (幂零)
-- 定理: Δⁿ ≡ 0 对所有 n ≥ 3
--
-- 代数本质: Δ = S - I, 在 char 3 上:
--   Δ³ = (S-I)³ = S³ - 3S² + 3S - I = S³ - I = 0
-- 连续微分无此性质: d³/dx³ 不恒为零。
--------------------------------------------------------------------------------

-- 迭代差分: Δ⁰ = id, Δⁿ⁺¹ = Δ ∘ Δⁿ
Δⁿ : ℕ → GF3Func → GF3Func
Δⁿ zero    f = f
Δⁿ (suc n) f = Δ (Δⁿ n f)

-- Δ⁰ 是恒等
Δ⁰≡id : ∀ f → Δⁿ 0 f ≡ f
Δ⁰≡id f = refl

-- Δ¹ 是 Δ
Δ¹≡Δ : ∀ f → Δⁿ 1 f ≡ Δ f
Δ¹≡Δ f = refl

-- Δ² 将任意函数坍缩为常数 (值 = 三值之和)
Δ²≡const : ∀ f → Δⁿ 2 f ≡ (sum3 f , sum3 f , sum3 f)
Δ²≡const f = Δ²-is-const f

-- 定理: Δⁿ ≡ 0 对所有 n ≥ 3
-- 证明: 对 n 归纳
--   基: Δ³f = 0 (Δ³≡0)
--   步: Δⁿ⁺³f = Δ(Δⁿ⁺²f) = Δ(0) = 0 (Δ-const-zero)
Δⁿ≥3≡0 : ∀ n f → Δⁿ (3 + n) f ≡ (T₀ , T₀ , T₀)
Δⁿ≥3≡0 zero    f = Δ³≡0 f
Δⁿ≥3≡0 (suc n) f = trans (cong Δ (Δⁿ≥3≡0 n f)) (Δ-const-zero T₀)

-- Δ² 的核刻画: Δ²f = 0 当且仅当 sum3(f) = 0
-- 正向: Δ²f = (s,s,s), 若 (s,s,s) = 0 则 s = 0
Δ²≡0→sum3≡0 : ∀ f → Δ (Δ f) ≡ (T₀ , T₀ , T₀) → sum3 f ≡ T₀
Δ²≡0→sum3≡0 f h = proj₁ (triple-decomp (trans (sym (Δ²-is-const f)) h))

-- 反向: sum3(f) = 0 → Δ²f = (0,0,0)
sum3≡0→Δ²≡0 : ∀ f → sum3 f ≡ T₀ → Δ (Δ f) ≡ (T₀ , T₀ , T₀)
sum3≡0→Δ²≡0 f h rewrite Δ²-is-const f | h = refl

--------------------------------------------------------------------------------
-- §3. GF3Func 求值与制表
--
-- GF3Func = Trit × Trit × Trit 是 Trit → Trit 的有限表示。
-- 求值和制表建立两者的桥接, 避免函数外延性公理。
--------------------------------------------------------------------------------

-- 求值: GF3Func → Trit → Trit
evalGF3 : GF3Func → Trit → Trit
evalGF3 (f₀ , f₁ , f₂) T₀ = f₀
evalGF3 (f₀ , f₁ , f₂) T₁ = f₁
evalGF3 (f₀ , f₁ , f₂) T₂ = f₂

-- 制表: (Trit → Trit) → GF3Func
tabulate : (Trit → Trit) → GF3Func
tabulate f = (f T₀ , f T₁ , f T₂)

-- 制表-求值互逆 (逐点)
eval-tab-pointwise : ∀ f x → evalGF3 (tabulate f) x ≡ f x
eval-tab-pointwise f T₀ = refl
eval-tab-pointwise f T₁ = refl
eval-tab-pointwise f T₂ = refl

-- 求值-制表互逆 (GF3Func 上)
tab-eval : ∀ g → tabulate (evalGF3 g) ≡ g
tab-eval (f₀ , f₁ , f₂) = refl

-- GF3Func 计数: 3³ = 27 (有限函数空间)
gf3func-count : 3 * 3 * 3 ≡ 27
gf3func-count = refl

--------------------------------------------------------------------------------
-- §4. 线性离散 ODE: Δy = g
--
-- 连续 ODE: dy/dx = g(x)
-- 离散 ODE: Δy(x) = g(x), 即 y(x⊕T₁) ⊖ y(x) = g(x)
--
-- Fredholm 相容性: sum3(g) = 0 (望远镜恒等式的推论)
-- 解的存在性: 当 sum3(g) = 0 时, y = (T₀, g₀, g₀⊕g₁) 是解
-- 解的唯一性: 两个解相差一个常数 (Δy = 0 → y 是常数)
--------------------------------------------------------------------------------

-- Fredholm 相容性 (必要条件): Δy = g 可解 → sum3(g) = 0
-- 证明: sum3(g) = sum3(Δy) = 0 (望远镜恒等式)
fredholm-compatibility : ∀ y g → Δ y ≡ g → sum3 g ≡ T₀
fredholm-compatibility y g h rewrite sym h = sum3-Δ≡0 y

-- 线性 ODE 解的构造
-- 给定 g = (g₀, g₁, g₂) 满足 g₀⊕g₁⊕g₂ = T₀,
-- 构造 y = (T₀, g₀, g₀⊕g₁) (初始条件 y(T₀) = T₀)
ode-solve : (g : GF3Func) → sum3 g ≡ T₀ → GF3Func
ode-solve (g₀ , g₁ , g₂) _ = (T₀ , g₀ , g₀ ⊕ g₁)

-- 解的正确性: Δ(ode-solve g) = g
-- 证明:
--   Δ(T₀, g₀, g₀⊕g₁) = (g₀⊕T₀, (g₀⊕g₁)⊕negate(g₀), T₀⊕negate(g₀⊕g₁))
--                      = (g₀, g₁, negate(g₀⊕g₁))
--                      = (g₀, g₁, g₂)  [由相容性条件]
ode-solve-correct : ∀ g₀ g₁ g₂ → (g₀ ⊕ g₁) ⊕ g₂ ≡ T₀ →
  Δ (T₀ , g₀ , g₀ ⊕ g₁) ≡ (g₀ , g₁ , g₂)
ode-solve-correct g₀ g₁ g₂ compat = triple-≡
  (⊕-identityʳ g₀)
  (⊕-cancelˡ g₀ g₁)
  (trans (⊕-identityˡ (negate (g₀ ⊕ g₁)))
         (sym (⊕-right-cancel (g₀ ⊕ g₁) g₂ compat)))

-- 包装版本: 对任意 g 和相容性证明
ode-solve-verified : ∀ g → (h : sum3 g ≡ T₀) → Δ (ode-solve g h) ≡ g
ode-solve-verified (g₀ , g₁ , g₂) h = ode-solve-correct g₀ g₁ g₂ h

-- 齐次方程 Δy = 0 的解是常数函数
-- 证明: Δy = 0 意味着 y₁-y₀=0, y₂-y₁=0, 所以 y₀=y₁=y₂
Δ≡0→const : ∀ y → Δ y ≡ (T₀ , T₀ , T₀) → Σ Trit (λ c → y ≡ (c , c , c))
Δ≡0→const (y₀ , y₁ , y₂) h = y₀ , triple-≡ refl eq₀₁ (trans eq₁₂ eq₀₁)
  where
    decomp = triple-decomp h
    eq₀₁ : y₁ ≡ y₀
    eq₀₁ = ⊕-negate≡0→≡ y₁ y₀ (proj₁ decomp)
    eq₁₂ : y₂ ≡ y₁
    eq₁₂ = ⊕-negate≡0→≡ y₂ y₁ (proj₁ (proj₂ decomp))

--------------------------------------------------------------------------------
-- §5. 非线性离散 ODE: Δy(x) = f(x, y(x))
--
-- 连续 ODE: dy/dx = f(x, y)
-- 离散 ODE: y(x⊕T₁) ⊖ y(x) = f(x, y(x))
--           y(x⊕T₁) = y(x) ⊕ f(x, y(x))
--
-- 在 GF(3) 上, f : Trit → Trit → Trit (9 个参数, 3⁹ = 19683 种)
-- 函数空间有限 (27 个), 所以解的存在性是可判定的
--------------------------------------------------------------------------------

-- 离散 ODE 的定义
-- f : Trit → Trit → Trit 是驱动函数
-- 解 y : GF3Func 满足 Δy = tabulate(λ x → f x (y x))
record DiscreteODE (f : Trit → Trit → Trit) : Set where
  field
    sol : GF3Func
    sat : Δ sol ≡ tabulate (λ x → f x (evalGF3 sol x))

-- 例 1: 零 ODE (f ≡ 0), 常数零函数是解
-- Δ(T₀,T₀,T₀) = (T₀,T₀,T₀) = tabulate(λ _ → T₀)
zero-ode : DiscreteODE (λ _ _ → T₀)
zero-ode = record
  { sol = (T₀ , T₀ , T₀)
  ; sat = refl
  }

-- 例 2: 常数驱动 ODE (f(x,y) ≡ T₁)
-- Δy = (T₁,T₁,T₁), 解 y = (T₀,T₁,T₂)
-- 验证: Δ(T₀,T₁,T₂) = (T₁⊕T₀, T₂⊕T₂, T₀⊕T₁) = (T₁,T₁,T₁)
const-driven-ode-T₁ : DiscreteODE (λ _ _ → T₁)
const-driven-ode-T₁ = record
  { sol = (T₀ , T₁ , T₂)
  ; sat = refl
  }

-- 例 3: 常数驱动 ODE (f(x,y) ≡ T₂)
-- Δy = (T₂,T₂,T₂), 解 y = (T₀,T₂,T₁)
-- 验证: Δ(T₀,T₂,T₁) = (T₂⊕T₀, T₁⊕T₁, T₀⊕T₂) = (T₂,T₂,T₂)
const-driven-ode-T₂ : DiscreteODE (λ _ _ → T₂)
const-driven-ode-T₂ = record
  { sol = (T₀ , T₂ , T₁)
  ; sat = refl
  }

-- 非线性 ODE 的 Fredholm 相容性
-- 如果 y 是 Δy = f(·, y(·)) 的解, 则 sum3(f(·, y(·))) = 0
-- 证明: sum3(f(·,y(·))) = sum3(Δy) = 0 (望远镜恒等式)
ode-fredholm : ∀ {f : Trit → Trit → Trit} → (ode : DiscreteODE f) →
  sum3 (tabulate (λ x → f x (evalGF3 (DiscreteODE.sol ode) x))) ≡ T₀
ode-fredholm {f} ode =
  let open DiscreteODE ode in
  trans (cong sum3 (sym sat)) (sum3-Δ≡0 sol)

--------------------------------------------------------------------------------
-- §6. 二维离散 PDE — 离散 Laplace 方程
--
-- 连续 PDE: ∂²u/∂x² + ∂²u/∂y² = 0 (Laplace 方程)
-- 离散 PDE: Δ₁²u + Δ₂²u = 0 (离散 Laplace)
--
-- 在 T⁶ = (Z/3Z)⁶ 上, 每个维度独立满足 Δᵢ³ ≡ 0。
-- 这里用 2D 切片 (Z/3Z)² 演示, 6D 推广是直接的:
-- 每个维度贡献一个 Δᵢ, 全部继承 1D 幂零性。
--------------------------------------------------------------------------------

-- 2D 函数空间: (Z/3Z)² → GF(3), 表示为 3×3 格点值
GF3Func2D : Set
GF3Func2D = GF3Func × GF3Func × GF3Func

-- 零函数
zero2D : GF3Func2D
zero2D = ((T₀ , T₀ , T₀) , (T₀ , T₀ , T₀) , (T₀ , T₀ , T₀))

-- 常数函数
const2D : Trit → GF3Func2D
const2D s = ((s , s , s) , (s , s , s) , (s , s , s))

-- 逐点加法 (GF3Func)
_⊕f_ : GF3Func → GF3Func → GF3Func
(a₀ , a₁ , a₂) ⊕f (b₀ , b₁ , b₂) = (a₀ ⊕ b₀ , a₁ ⊕ b₁ , a₂ ⊕ b₂)

-- 逐点加法 (GF3Func2D)
_⊕2D_ : GF3Func2D → GF3Func2D → GF3Func2D
(r₀ , r₁ , r₂) ⊕2D (s₀ , s₁ , s₂) = (r₀ ⊕f s₀ , r₁ ⊕f s₁ , r₂ ⊕f s₂)

-- 第一维差分: 对每行应用 Δ
Δ₁ : GF3Func2D → GF3Func2D
Δ₁ (r₀ , r₁ , r₂) = (Δ r₀ , Δ r₁ , Δ r₂)

-- 转置: 行列互换
transpose2D : GF3Func2D → GF3Func2D
transpose2D ((a₀₀ , a₀₁ , a₀₂) , (a₁₀ , a₁₁ , a₁₂) , (a₂₀ , a₂₁ , a₂₂)) =
  ((a₀₀ , a₁₀ , a₂₀) , (a₀₁ , a₁₁ , a₂₁) , (a₀₂ , a₁₂ , a₂₂))

-- 第二维差分: 共轭 Δ₂ = T ∘ Δ₁ ∘ T
Δ₂ : GF3Func2D → GF3Func2D
Δ₂ u = transpose2D (Δ₁ (transpose2D u))

-- 离散 Laplace 算子: L = Δ₁² + Δ₂²
discrete-laplacian : GF3Func2D → GF3Func2D
discrete-laplacian u = Δ₁ (Δ₁ u) ⊕2D Δ₂ (Δ₂ u)

-- 调和函数: Lu = 0
Harmonic : GF3Func2D → Set
Harmonic u = discrete-laplacian u ≡ zero2D

-- 2D 等式构造
func2d-≡ : ∀ {r₀ r₁ r₂ s₀ s₁ s₂ : GF3Func} →
  r₀ ≡ s₀ → r₁ ≡ s₁ → r₂ ≡ s₂ → (r₀ , r₁ , r₂) ≡ (s₀ , s₁ , s₂)
func2d-≡ refl refl refl = refl

-- Δ₁ 的幂零性: Δ₁³ ≡ 0 (继承自 1D Δ³ ≡ 0, 逐行应用)
Δ₁³≡0 : ∀ u → Δ₁ (Δ₁ (Δ₁ u)) ≡ zero2D
Δ₁³≡0 (r₀ , r₁ , r₂) = func2d-≡ (Δ³≡0 r₀) (Δ³≡0 r₁) (Δ³≡0 r₂)

-- 转置是对合: T² = id
transpose²≡id : ∀ u → transpose2D (transpose2D u) ≡ u
transpose²≡id ((a₀₀ , a₀₁ , a₀₂) , (a₁₀ , a₁₁ , a₁₂) , (a₂₀ , a₂₁ , a₂₂)) = refl

-- Δ₂² 展开: Δ₂²u = T(Δ₁²(Tu))
Δ₂²-unfold : ∀ u → Δ₂ (Δ₂ u) ≡ transpose2D (Δ₁ (Δ₁ (transpose2D u)))
Δ₂²-unfold u =
  cong (λ x → transpose2D (Δ₁ x)) (transpose²≡id (Δ₁ (transpose2D u)))

-- Δ₂ 的幂零性: Δ₂³ ≡ 0
-- 证明: Δ₂³ = (T∘Δ₁∘T)³ = T∘Δ₁∘T²∘Δ₁∘T²∘Δ₁∘T = T∘Δ₁³∘T = T∘0∘T = 0
Δ₂³≡0 : ∀ u → Δ₂ (Δ₂ (Δ₂ u)) ≡ zero2D
Δ₂³≡0 u = begin
  Δ₂ (Δ₂ (Δ₂ u))
    ≡⟨ refl ⟩
  transpose2D (Δ₁ (transpose2D (Δ₂ (Δ₂ u))))
    ≡⟨ cong (λ x → transpose2D (Δ₁ x))
         (trans (cong transpose2D (Δ₂²-unfold u))
                (transpose²≡id (Δ₁ (Δ₁ (transpose2D u))))) ⟩
  transpose2D (Δ₁ (Δ₁ (Δ₁ (transpose2D u))))
    ≡⟨ cong transpose2D (Δ₁³≡0 (transpose2D u)) ⟩
  transpose2D zero2D
    ≡⟨ refl ⟩
  zero2D
  ∎
  where open ≡-Reasoning

-- Δ₁ 消灭常数函数
Δ₁-const-zero : ∀ s → Δ₁ (const2D s) ≡ zero2D
Δ₁-const-zero s = func2d-≡ (Δ-const-zero s) (Δ-const-zero s) (Δ-const-zero s)

-- Δ₂ 消灭常数函数 (通过共轭)
Δ₂-const-zero : ∀ s → Δ₂ (const2D s) ≡ zero2D
Δ₂-const-zero s = cong transpose2D (Δ₁-const-zero s)

-- Δ₁² 消灭常数函数
Δ₁²-const-zero : ∀ s → Δ₁ (Δ₁ (const2D s)) ≡ zero2D
Δ₁²-const-zero s = trans (cong Δ₁ (Δ₁-const-zero s)) (Δ₁-const-zero T₀)

-- Δ₂² 消灭常数函数
Δ₂²-const-zero : ∀ s → Δ₂ (Δ₂ (const2D s)) ≡ zero2D
Δ₂²-const-zero s = trans (cong Δ₂ (Δ₂-const-zero s)) (Δ₂-const-zero T₀)

-- 定理: 常数函数是调和的 (L(const) = 0)
-- 离散 Laplace 方程 Δ₁²u + Δ₂²u = 0 的最简单解
const-harmonic : ∀ s → Harmonic (const2D s)
const-harmonic s = cong₂ _⊕2D_ (Δ₁²-const-zero s) (Δ₂²-const-zero s)

--------------------------------------------------------------------------------
-- §7. 幂零性推论 — ≥3 阶离散 ODE 的平凡性
--
-- 连续 ODE: y⁽ⁿ⁾ = f(x, y, y', ..., y⁽ⁿ⁻¹⁾) 对任意 n 有非平凡解
-- 离散 ODE: Δⁿy = f(...) 对 n ≥ 3, 左端恒为零
--
-- 推论: 所有 ≥3 阶齐次离散 ODE 的解空间 = Δ² 的核
-- 即 sum3(y) = 0 的函数空间 (9 个函数, 3² = 9)
--------------------------------------------------------------------------------

-- ≥3 阶齐次 ODE Δⁿy = 0 等价于 Δ³y = 0 (因为 Δⁿy = 0 自动成立)
-- 具体地: Δ⁴y = Δ(Δ³y) = Δ(0) = 0
Δ⁴≡0 : ∀ f → Δⁿ 4 f ≡ (T₀ , T₀ , T₀)
Δ⁴≡0 f = Δⁿ≥3≡0 1 f

-- Δ⁵y = 0
Δ⁵≡0 : ∀ f → Δⁿ 5 f ≡ (T₀ , T₀ , T₀)
Δ⁵≡0 f = Δⁿ≥3≡0 2 f

-- 解空间计数: Δ²y = 0 的解满足 sum3(y) = 0
-- 即 y₀⊕y₁⊕y₂ = 0, 自由变量 y₀, y₁ ∈ GF(3), y₂ = negate(y₀⊕y₁)
-- 共 3² = 9 个解
kernel-count : 3 * 3 ≡ 9
kernel-count = refl

-- 与连续 ODE 的对比:
-- 连续 n 阶齐次 ODE 的解空间是 n 维 (由初始条件 y(0), y'(0), ..., y⁽ⁿ⁻¹⁾(0) 决定)
-- 离散 n 阶齐次 ODE (n ≥ 3) 的解空间是 2 维 (由 y(T₀), y(T₁) 决定, y(T₂) 被约束)
-- 幂零性截断了高阶自由度

--------------------------------------------------------------------------------
-- §8. 与连续 DE 的投影关系
--
-- 连续 ODE 是离散 ODE 在"步长→0"下的投影。
-- 但步长→0 在 GF(3) 中不存在 (步长固定为 T₁ = 1)。
-- 所以连续 ODE 是离散 ODE 的"不存在的极限"。
--
-- 投影丢失:
--   幂零性 Δ³=0 → 连续微分 d³/dx³ ≠ 0 (一般)
--   有限函数空间 27 → 无穷维函数空间
--   固定步长 1 → 可变步长 h→0
--   有限解空间 → 无穷维解空间
--------------------------------------------------------------------------------

-- 离散 DE 与连续 DE 的结构对比记录
record DiscreteVsContinuousDE : Set where
  constructor mkDiscreteVsContinuous
  field
    -- 离散步长 (GF(3) 上固定为 1, 不会 → 0)
    discrete-step : ℕ
    step-fixed : discrete-step ≡ 1
    -- 差分算子
    diff-operator : GF3Func → GF3Func
    -- 幂零性: Δ³ = 0 (连续微分无此性质)
    nilpotent-3 : ∀ f → diff-operator (diff-operator (diff-operator f)) ≡ (T₀ , T₀ , T₀)
    -- 步长非零: 极限 h→0 在 GF(3) 中不存在
    step-is-nonzero : T₁ ≢ T₀
    -- 函数空间有限: 27 个 (连续函数空间无穷维)
    func-space-size : ℕ
    func-space-finite : func-space-size ≡ 27
    -- 所有 ≥3 阶导数恒为零 (连续微分无此截断)
    higher-vanish : ∀ n f → Δⁿ (3 + n) f ≡ (T₀ , T₀ , T₀)

-- GF(3) 离散 DE 的见证
gf3-discrete-de : DiscreteVsContinuousDE
gf3-discrete-de = mkDiscreteVsContinuous
  1
  refl
  Δ
  Δ³≡0
  (λ ())
  27
  refl
  Δⁿ≥3≡0

-- 步长非零: 差分 ≠ 微分的核心证据
-- T₁ ≢ T₀ 意味着步长 h = 1 ≠ 0
-- 在 GF(3) 的离散拓扑中, 没有"趋近"的概念
-- 不存在 0 < |h| < 1 的 h (没有无穷小)
step-not-infinitesimal : T₁ ≢ T₀
step-not-infinitesimal = step-nonzero

-- GF(3) 中 T₁ 和 T₂ 不可混淆 — 没有"无穷小"
-- 任何声称 T₁ ≡ T₂ 的证明都是矛盾的
gf3-T₁≢T₂ : T₁ ≢ T₂
gf3-T₁≢T₂ ()

-- 非零元素不是零: T₂ 也不是无穷小
gf3-T₂≢T₀ : T₂ ≢ T₀
gf3-T₂≢T₀ ()

--------------------------------------------------------------------------------
-- 总结
--
-- 离散 ODE (GF(3)):
--   Δy = g 可解 ⟺ sum3(g) = 0 (Fredholm 相容性)
--   解 = 特解 + 常数 (齐次解空间 = 常数函数)
--   Δⁿy = 0 对 n ≥ 3 自动成立 (幂零截断)
--
-- 离散 PDE (2D):
--   Δ₁²u + Δ₂²u = 0 (离散 Laplace)
--   Δ₁³ = Δ₂³ = 0 (逐维幂零)
--   常数函数是调和的
--
-- 投影丢失:
--   幂零性 (Δ³=0) → 连续微分无此性质
--   有限函数空间 (27) → 无穷维
--   固定步长 (1) → 极限 h→0 不存在
--   有限解空间 → 无穷维解空间
--------------------------------------------------------------------------------
