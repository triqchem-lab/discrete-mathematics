{-# OPTIONS --rewriting #-}
module Sovereign.Algebra.ProjectionDifferential where

--------------------------------------------------------------------------------
-- 投影微分/算子 — MSC 34-35 (ODE/PDE) 与 MSC 46-47 (泛函/算子) 的离散本源
--
-- 核心原则: 本体是离散涡旋数学, 投影是连续统近似。
-- 不定义连续统对象本身 (Banach 空间、微分算子等)。
--
-- MSC 34-35: GF(3) 差分方程 → 连续微分方程
--   差分算子 Δf(x) = f(x⊕T₁) ⊖ f(x), 步长固定为 1
--   连续极限 lim_{h→0} 在 GF(3) 中不存在 (T₁ ≢ T₀)
--   Δ³ ≡ 0 (三阶幂零, 连续微分无此性质)
--
-- MSC 46-47: GF(3) 有限维矩阵 → 无穷维算子
--   2×2 矩阵: 3⁴ = 81 个, 谱至多 2 个特征值 (离散)
--   无穷维算子: 谱可连续 (投影丢失离散性)
--
-- 退化分类学连接:
--   eval₀ : GF3Func → Trit (求值退化 + 常数截面)
--   trace : Mat2x2 → Trit  (迹退化 + 标量截面)
--
-- 0 postulate — 全部构造性证明
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using (
  Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; negate²;
  ⊕-identityˡ; ⊕-identityʳ; ⊗-identityʳ; ⊗-zeroʳ)
open import Sovereign.Algebra.DegenerationTaxonomy using (
  Degeneration; Section; not-injective; mk-degeneration)

--------------------------------------------------------------------------------
-- §1. GF(3) 函数空间与差分算子 (MSC 34-35)
--
-- GF(3) 上的函数 f : Trit → Trit 由三个值 (f(T₀), f(T₁), f(T₂)) 完全决定。
-- 用三元组表示, 避免函数外延性公理。
-- 共 3³ = 27 个函数。
--------------------------------------------------------------------------------

GF3Func : Set
GF3Func = Trit × Trit × Trit  -- (f(T₀), f(T₁), f(T₂))

-- 三元组求和: sum3(f) = f(T₀) ⊕ f(T₁) ⊕ f(T₂)
sum3 : GF3Func → Trit
sum3 (a , b , c) = (a ⊕ b) ⊕ c

-- 移位算子 S: Sf(x) = f(x ⊕ T₁)
-- 在 GF(3) 上, x ⊕ T₁ 是循环移位: T₀→T₁→T₂→T₀
-- 因此 S(f₀, f₁, f₂) = (f₁, f₂, f₀) — 三元组左循环
shift : GF3Func → GF3Func
shift (f₀ , f₁ , f₂) = (f₁ , f₂ , f₀)

-- 差分算子 Δ: Δf(x) = f(x⊕T₁) ⊖ f(x) = f(x⊕T₁) ⊕ negate(f(x))
-- 即 Δ = S - I (移位减恒等)
Δ : GF3Func → GF3Func
Δ (f₀ , f₁ , f₂) = (f₁ ⊕ negate f₀ , f₂ ⊕ negate f₁ , f₀ ⊕ negate f₂)

--------------------------------------------------------------------------------
-- §2. 移位算子的周期性 — S³ = id
--
-- GF(3) 只有 3 个元素, 移位 3 次回到原位。
-- 连续平移无此性质 (ℝ 上平移无周期)。
--------------------------------------------------------------------------------

shift³≡id : ∀ f → shift (shift (shift f)) ≡ f
shift³≡id (f₀ , f₁ , f₂) = refl

-- 移位非恒等: S ≠ I (差分的步长非零)
-- 见证: f = (T₀, T₁, T₀), Sf = (T₁, T₀, T₀) ≠ f
shift≠id : Σ GF3Func (λ f → shift f ≢ f)
shift≠id = (T₀ , T₁ , T₀) , (λ ())

--------------------------------------------------------------------------------
-- §3. 差分算子的幂零性 — Δ³ ≡ 0
--
-- 代数本质: Δ = S - I, 在 GF(3) 上:
--   Δ³ = (S-I)³ = S³ - 3S² + 3S - I = S³ - I = 0
-- 因为 S³ = I (周期 3) 且 3 = 0 (char 3)。
--
-- 连续微分无此性质: d³/dx³ 不恒为零。
-- 这是离散与连续的根本截断误差。
--------------------------------------------------------------------------------

-- 引理 1: 常数函数的差分为零
Δ-const-zero : ∀ s → Δ (s , s , s) ≡ (T₀ , T₀ , T₀)
Δ-const-zero T₀ = refl
Δ-const-zero T₁ = refl
Δ-const-zero T₂ = refl

-- 引理 2: 二阶差分将任意函数坍缩为常数 (值 = 三值之和)
-- Δ²(f₀,f₁,f₂) = (s,s,s), s = f₀⊕f₁⊕f₂
-- 27 case 穷举 (GF(3) 算术归约)
Δ²-is-const : ∀ f → Δ (Δ f) ≡ (sum3 f , sum3 f , sum3 f)
Δ²-is-const (T₀ , T₀ , T₀) = refl
Δ²-is-const (T₀ , T₀ , T₁) = refl
Δ²-is-const (T₀ , T₀ , T₂) = refl
Δ²-is-const (T₀ , T₁ , T₀) = refl
Δ²-is-const (T₀ , T₁ , T₁) = refl
Δ²-is-const (T₀ , T₁ , T₂) = refl
Δ²-is-const (T₀ , T₂ , T₀) = refl
Δ²-is-const (T₀ , T₂ , T₁) = refl
Δ²-is-const (T₀ , T₂ , T₂) = refl
Δ²-is-const (T₁ , T₀ , T₀) = refl
Δ²-is-const (T₁ , T₀ , T₁) = refl
Δ²-is-const (T₁ , T₀ , T₂) = refl
Δ²-is-const (T₁ , T₁ , T₀) = refl
Δ²-is-const (T₁ , T₁ , T₁) = refl
Δ²-is-const (T₁ , T₁ , T₂) = refl
Δ²-is-const (T₁ , T₂ , T₀) = refl
Δ²-is-const (T₁ , T₂ , T₁) = refl
Δ²-is-const (T₁ , T₂ , T₂) = refl
Δ²-is-const (T₂ , T₀ , T₀) = refl
Δ²-is-const (T₂ , T₀ , T₁) = refl
Δ²-is-const (T₂ , T₀ , T₂) = refl
Δ²-is-const (T₂ , T₁ , T₀) = refl
Δ²-is-const (T₂ , T₁ , T₁) = refl
Δ²-is-const (T₂ , T₁ , T₂) = refl
Δ²-is-const (T₂ , T₂ , T₀) = refl
Δ²-is-const (T₂ , T₂ , T₁) = refl
Δ²-is-const (T₂ , T₂ , T₂) = refl

-- 定理: 三阶差分恒为零
-- 代数本质: Δ²f = (s,s,s) (常数), Δ(s,s,s) = (T₀,T₀,T₀)
-- 27 case 穷举验证
Δ³≡0 : ∀ f → Δ (Δ (Δ f)) ≡ (T₀ , T₀ , T₀)
Δ³≡0 (T₀ , T₀ , T₀) = refl
Δ³≡0 (T₀ , T₀ , T₁) = refl
Δ³≡0 (T₀ , T₀ , T₂) = refl
Δ³≡0 (T₀ , T₁ , T₀) = refl
Δ³≡0 (T₀ , T₁ , T₁) = refl
Δ³≡0 (T₀ , T₁ , T₂) = refl
Δ³≡0 (T₀ , T₂ , T₀) = refl
Δ³≡0 (T₀ , T₂ , T₁) = refl
Δ³≡0 (T₀ , T₂ , T₂) = refl
Δ³≡0 (T₁ , T₀ , T₀) = refl
Δ³≡0 (T₁ , T₀ , T₁) = refl
Δ³≡0 (T₁ , T₀ , T₂) = refl
Δ³≡0 (T₁ , T₁ , T₀) = refl
Δ³≡0 (T₁ , T₁ , T₁) = refl
Δ³≡0 (T₁ , T₁ , T₂) = refl
Δ³≡0 (T₁ , T₂ , T₀) = refl
Δ³≡0 (T₁ , T₂ , T₁) = refl
Δ³≡0 (T₁ , T₂ , T₂) = refl
Δ³≡0 (T₂ , T₀ , T₀) = refl
Δ³≡0 (T₂ , T₀ , T₁) = refl
Δ³≡0 (T₂ , T₀ , T₂) = refl
Δ³≡0 (T₂ , T₁ , T₀) = refl
Δ³≡0 (T₂ , T₁ , T₁) = refl
Δ³≡0 (T₂ , T₁ , T₂) = refl
Δ³≡0 (T₂ , T₂ , T₀) = refl
Δ³≡0 (T₂ , T₂ , T₁) = refl
Δ³≡0 (T₂ , T₂ , T₂) = refl

--------------------------------------------------------------------------------
-- §4. 望远镜恒等式 — sum3(Δf) ≡ T₀
--
-- 离散版 "全微分积分为零":
--   (f₁-f₀) + (f₂-f₁) + (f₀-f₂) = 0
-- 这是差分方程 Δf = g 可解的必要条件 (Fredholm 相容性)。
--------------------------------------------------------------------------------

sum3-Δ≡0 : ∀ f → sum3 (Δ f) ≡ T₀
sum3-Δ≡0 (T₀ , T₀ , T₀) = refl
sum3-Δ≡0 (T₀ , T₀ , T₁) = refl
sum3-Δ≡0 (T₀ , T₀ , T₂) = refl
sum3-Δ≡0 (T₀ , T₁ , T₀) = refl
sum3-Δ≡0 (T₀ , T₁ , T₁) = refl
sum3-Δ≡0 (T₀ , T₁ , T₂) = refl
sum3-Δ≡0 (T₀ , T₂ , T₀) = refl
sum3-Δ≡0 (T₀ , T₂ , T₁) = refl
sum3-Δ≡0 (T₀ , T₂ , T₂) = refl
sum3-Δ≡0 (T₁ , T₀ , T₀) = refl
sum3-Δ≡0 (T₁ , T₀ , T₁) = refl
sum3-Δ≡0 (T₁ , T₀ , T₂) = refl
sum3-Δ≡0 (T₁ , T₁ , T₀) = refl
sum3-Δ≡0 (T₁ , T₁ , T₁) = refl
sum3-Δ≡0 (T₁ , T₁ , T₂) = refl
sum3-Δ≡0 (T₁ , T₂ , T₀) = refl
sum3-Δ≡0 (T₁ , T₂ , T₁) = refl
sum3-Δ≡0 (T₁ , T₂ , T₂) = refl
sum3-Δ≡0 (T₂ , T₀ , T₀) = refl
sum3-Δ≡0 (T₂ , T₀ , T₁) = refl
sum3-Δ≡0 (T₂ , T₀ , T₂) = refl
sum3-Δ≡0 (T₂ , T₁ , T₀) = refl
sum3-Δ≡0 (T₂ , T₁ , T₁) = refl
sum3-Δ≡0 (T₂ , T₁ , T₂) = refl
sum3-Δ≡0 (T₂ , T₂ , T₀) = refl
sum3-Δ≡0 (T₂ , T₂ , T₁) = refl
sum3-Δ≡0 (T₂ , T₂ , T₂) = refl

--------------------------------------------------------------------------------
-- §5. 步长固定性 — 差分 ≠ 微分
--
-- 连续微分: df/dx = lim_{h→0} (f(x+h)-f(x))/h
-- 离散差分: Δf(x) = f(x⊕T₁) ⊖ f(x), 步长 h = T₁ (固定)
--
-- 截断误差的本质: T₁ ≢ T₀, 即 h = 1 ≠ 0。
-- 在 GF(3) 的离散拓扑中, 没有 "趋近" 的概念,
-- 极限 lim_{h→0} 不存在于 GF(3)。
--------------------------------------------------------------------------------

-- 步长非零: 差分步长 T₁ 不等于零 T₀
step-nonzero : T₁ ≢ T₀
step-nonzero ()

-- 差分 vs 微分的结构记录
-- 记录离散差分的本质特征, 不定义连续微分 (连续统不是本体)
record DifferenceVsDifferential : Set where
  constructor mkDiffVsDiff
  field
    -- 离散步长 (GF(3) 上固定为 1, 不会 → 0)
    discrete-step : ℕ
    step-fixed : discrete-step ≡ 1
    -- 差分算子
    diff-operator : GF3Func → GF3Func
    -- 幂零性: Δ³ = 0 (连续微分无此性质)
    diff-nilpotent : ∀ f → diff-operator (diff-operator (diff-operator f)) ≡ (T₀ , T₀ , T₀)
    -- 步长非零: 极限 h→0 在 GF(3) 中不存在
    step-is-nonzero : T₁ ≢ T₀

-- GF(3) 差分的见证
gf3-difference : DifferenceVsDifferential
gf3-difference = mkDiffVsDiff
  1
  refl
  Δ
  Δ³≡0
  (λ ())

--------------------------------------------------------------------------------
-- §6. GF(3) 上的矩阵代数 (MSC 46-47)
--
-- 2×2 矩阵: 4 个 GF(3) 元素, 共 3⁴ = 81 个矩阵。
-- 有限维: 谱是离散有限集 (至多 2 个特征值)。
-- 无穷维投影: 谱可连续 (丢失离散性)。
--------------------------------------------------------------------------------

record Mat2x2 : Set where
  constructor mkMat
  field
    m₀₀ m₀₁ m₁₀ m₁₁ : Trit

-- 迹: tr(A) = a₀₀ + a₁₁
trace : Mat2x2 → Trit
trace A = let open Mat2x2 A in m₀₀ ⊕ m₁₁

-- 行列式: det(A) = a₀₀·a₁₁ - a₀₁·a₁₀
det : Mat2x2 → Trit
det A = let open Mat2x2 A in (m₀₀ ⊗ m₁₁) ⊕ negate (m₀₁ ⊗ m₁₀)

-- 矩阵计数: 4 个 GF(3) 元素 → 3⁴ = 81 个矩阵
mat2x2-count : 3 * 3 * 3 * 3 ≡ 81
mat2x2-count = refl

-- 矩阵维度
mat2x2-dim : ℕ
mat2x2-dim = 2

mat2x2-entries : ℕ
mat2x2-entries = 4  -- dim² = 2² = 4

mat2x2-entries-correct : mat2x2-entries ≡ 2 * 2
mat2x2-entries-correct = refl

--------------------------------------------------------------------------------
-- §7. 特征多项式与谱的离散性
--
-- 特征多项式: p(λ) = λ² - tr(A)·λ + det(A)
-- 在 GF(3) 上: p(λ) = λ⊗λ ⊕ negate(tr(A)⊗λ) ⊕ det(A)
--
-- 关键定理: 二次多项式在 GF(3) 上至多 2 个根。
-- 因此 2×2 矩阵至多 2 个特征值 — 谱是离散有限集。
--------------------------------------------------------------------------------

-- 特征多项式求值
charPoly : Mat2x2 → Trit → Trit
charPoly A x = ((x ⊗ x) ⊕ negate ((trace A) ⊗ x)) ⊕ det A

-- 特征值谓词: x 是 A 的特征值 ⟺ p(x) = 0
IsEigenvalue : Mat2x2 → Trit → Set
IsEigenvalue A x = charPoly A x ≡ T₀

-- 谱: 所有特征值的集合 (GF(3) 的子集)
Spectrum : Mat2x2 → Set
Spectrum A = Σ Trit (λ x → IsEigenvalue A x)

-- 特征多项式在 T₀ 处的值 = det(A)
charPoly-T₀ : ∀ A → charPoly A T₀ ≡ det A
charPoly-T₀ A rewrite ⊗-zeroʳ (trace A) = refl

-- 特征多项式在 T₁ 处的值 = (T₁ ⊕ negate(tr(A))) ⊕ det(A)
charPoly-T₁ : ∀ A → charPoly A T₁ ≡ (T₁ ⊕ negate (trace A)) ⊕ det A
charPoly-T₁ A rewrite ⊗-identityʳ (trace A) = refl

-- 特征多项式在 T₂ 处的值 = (T₁ ⊕ negate(tr(A)⊗T₂)) ⊕ det(A)
charPoly-T₂ : ∀ A → charPoly A T₂ ≡ (T₁ ⊕ negate (trace A ⊗ T₂)) ⊕ det A
charPoly-T₂ A = refl

-- 二次多项式在 GF(3) 上不可能三个元素都是根
-- p(λ) = λ² ⊕ a⊗λ ⊕ b, 对任意 a, b ∈ GF(3):
-- p(T₀), p(T₁), p(T₂) 不可能同时为 T₀
-- 9 case 穷举 (tr, det 各 3 种)
quad-not-all-roots : ∀ a b →
  b ≡ T₀ →
  ((T₁ ⊕ negate a) ⊕ b) ≡ T₀ →
  ((T₁ ⊕ negate (a ⊗ T₂)) ⊕ b) ≡ T₀ →
  ⊥
quad-not-all-roots T₀ T₀ _ () _   -- p(T₁) = T₁ ≢ T₀
quad-not-all-roots T₀ T₁ () _ _   -- p(T₀) = T₁ ≢ T₀
quad-not-all-roots T₀ T₂ () _ _   -- p(T₀) = T₂ ≢ T₀
quad-not-all-roots T₁ T₀ _ _ ()   -- p(T₂) = T₂ ≢ T₀
quad-not-all-roots T₁ T₁ () _ _   -- p(T₀) = T₁ ≢ T₀
quad-not-all-roots T₁ T₂ () _ _   -- p(T₀) = T₂ ≢ T₀
quad-not-all-roots T₂ T₀ _ () _   -- p(T₁) = T₂ ≢ T₀
quad-not-all-roots T₂ T₁ () _ _   -- p(T₀) = T₁ ≢ T₀
quad-not-all-roots T₂ T₂ () _ _   -- p(T₀) = T₂ ≢ T₀

-- 定理: 2×2 矩阵至多 2 个特征值
-- 证明: 若 T₀, T₁, T₂ 都是特征值, 则 charPoly 在三点都为 T₀,
-- 但 quad-not-all-roots 证明这不可能。
at-most-2-eigenvalues : ∀ A →
  ¬ (IsEigenvalue A T₀ × IsEigenvalue A T₁ × IsEigenvalue A T₂)
at-most-2-eigenvalues A (ev₀ , ev₁ , ev₂) =
  quad-not-all-roots (trace A) (det A)
    (trans (sym (charPoly-T₀ A)) ev₀)
    (trans (sym (charPoly-T₁ A)) ev₁)
    (trans (sym (charPoly-T₂ A)) ev₂)

-- 谱离散性: 谱是 GF(3) 的有限子集, 至多 3 个元素
-- (由 at-most-2-eigenvalues 加强为至多 2 个)
-- 连续统中无穷维算子的谱可以是连续集 (如 [0,1] ⊂ ℝ),
-- 这在 GF(3) 中不可能: 谱 ⊆ {T₀, T₁, T₂}, 天然有限。
spectrum-finite : ∀ A → Spectrum A → Σ Trit (λ x → IsEigenvalue A x)
spectrum-finite A (x , ev) = x , ev

--------------------------------------------------------------------------------
-- §8. 有限维 vs 无穷维 — 投影丢失记录
--
-- 不定义 Banach 空间或无穷维算子 (连续统不是本体)。
-- 仅记录有限维的离散性质, 这些性质在无穷维投影中丢失。
--------------------------------------------------------------------------------

record FiniteVsInfinite : Set where
  constructor mkFinVsInf
  field
    -- 有限维: GF(3) 矩阵维度
    finite-dim : ℕ
    -- 矩阵数量: 3^(dim²)
    matrix-count : ℕ
    count-correct : matrix-count ≡ 81  -- 3⁴ for 2×2
    -- 谱上界: 至多 dim 个特征值
    spectrum-bound : ℕ
    spectrum-bound-correct : spectrum-bound ≡ 2
    -- 谱离散性证据: 不可能所有 GF(3) 元素都是特征值
    spectrum-discrete : ∀ A → ¬ (IsEigenvalue A T₀ × IsEigenvalue A T₁ × IsEigenvalue A T₂)

-- GF(3) 2×2 矩阵的见证
gf3-finite-operators : FiniteVsInfinite
gf3-finite-operators = mkFinVsInf
  2
  81
  refl
  2
  refl
  at-most-2-eigenvalues

--------------------------------------------------------------------------------
-- §9. 退化分类学连接 — DegenerationTaxonomy 实例
--
-- 复用 Degeneration 和 Section record, 构造具体实例:
--   eval₀ : GF3Func → Trit (MSC 34-35: 求值丢失差分信息)
--   trace : Mat2x2 → Trit  (MSC 46-47: 迹丢失谱信息)
--------------------------------------------------------------------------------

-- 9a. 求值映射 (MSC 34-35)
-- eval₀(f) = f(T₀): 将函数坍缩为单点值, 丢失全部差分/导数信息

eval₀ : GF3Func → Trit
eval₀ (f₀ , f₁ , f₂) = f₀

-- eval₀ 不是单射: 不同函数可以有相同的 T₀ 值
-- 见证: 常数零函数 vs 非零函数, 在 T₀ 处值相同
eval₀-x : GF3Func
eval₀-x = (T₀ , T₀ , T₀)

eval₀-y : GF3Func
eval₀-y = (T₀ , T₁ , T₀)

eval₀-witness-neq : eval₀-x ≢ eval₀-y
eval₀-witness-neq ()

eval₀-witness-eq : eval₀ eval₀-x ≡ eval₀ eval₀-y
eval₀-witness-eq = refl

eval₀-not-injective : not-injective {GF3Func} {Trit} eval₀
eval₀-not-injective = eval₀-x , (eval₀-y , (eval₀-witness-neq , eval₀-witness-eq))

-- 退化实例: 求值退化
eval₀-degeneration : Degeneration GF3Func Trit
eval₀-degeneration = mk-degeneration {GF3Func} {Trit} eval₀ eval₀-not-injective

-- eval₀ 有截面: 常数函数嵌入
-- const(a) = (a, a, a), eval₀(const(a)) = a
const-func : Trit → GF3Func
const-func a = (a , a , a)

eval₀-const-valid : ∀ a → eval₀ (const-func a) ≡ a
eval₀-const-valid a = refl

-- 截面不可逆证据: const(T₀) = (T₀,T₀,T₀) ≠ (T₀,T₁,T₀)
eval₀-sec-neq : const-func T₀ ≢ eval₀-y
eval₀-sec-neq ()

-- 截面实例: 求值截面 (有效但不完整)
-- 常数函数是有效截面, 但大多数函数不是常数
eval₀-section : Section GF3Func Trit
eval₀-section = record
  { projection    = eval₀
  ; section       = const-func
  ; section-valid = eval₀-const-valid
  ; not-surjective = eval₀-y , (T₀ , eval₀-sec-neq)
  }

-- 9b. 迹映射 (MSC 46-47)
-- trace(A) = a₀₀ + a₁₁: 将矩阵坍缩为标量, 丢失谱结构

-- trace 不是单射: 不同矩阵可以有相同的迹
trace-x : Mat2x2
trace-x = mkMat T₁ T₀ T₀ T₀

trace-y : Mat2x2
trace-y = mkMat T₀ T₀ T₀ T₁

trace-witness-neq : trace-x ≢ trace-y
trace-witness-neq ()

trace-witness-eq : trace trace-x ≡ trace trace-y
trace-witness-eq = refl

trace-not-injective : not-injective {Mat2x2} {Trit} trace
trace-not-injective = trace-x , (trace-y , (trace-witness-neq , trace-witness-eq))

-- 退化实例: 迹退化
trace-degeneration : Degeneration Mat2x2 Trit
trace-degeneration = mk-degeneration {Mat2x2} {Trit} trace trace-not-injective

-- trace 有截面: 标量矩阵嵌入
-- scalar(a) = [[a, 0], [0, 0]], trace(scalar(a)) = a + 0 = a
scalar-mat : Trit → Mat2x2
scalar-mat a = mkMat a T₀ T₀ T₀

trace-scalar-valid : ∀ a → trace (scalar-mat a) ≡ a
trace-scalar-valid a = ⊕-identityʳ a

-- 截面不可逆证据: scalar(T₀) = [[0,0],[0,0]] ≠ [[0,1],[0,0]]
trace-sec-t : Mat2x2
trace-sec-t = mkMat T₀ T₁ T₀ T₀

trace-sec-neq : scalar-mat T₀ ≢ trace-sec-t
trace-sec-neq ()

-- 截面实例: 迹截面 (有效但不完整)
-- 标量矩阵是有效截面, 但大多数矩阵不是标量矩阵
trace-section : Section Mat2x2 Trit
trace-section = record
  { projection    = trace
  ; section       = scalar-mat
  ; section-valid = trace-scalar-valid
  ; not-surjective = trace-sec-t , (T₀ , trace-sec-neq)
  }

--------------------------------------------------------------------------------
-- §10. 投影丢失总结
--
-- MSC 34-35 (ODE/PDE):
--   本体: GF(3) 差分算子 Δ, 步长 = 1 (固定), Δ³ = 0
--   投影: 连续微分 d/dx, 步长 h → 0 (极限), d³/dx³ ≠ 0 (一般)
--   丢失: 幂零性 (Δ³=0), 周期性 (S³=I), 有限函数空间 (27 个)
--   截断: T₁ ≢ T₀, 极限不存在于 GF(3)
--
-- MSC 46-47 (泛函/算子):
--   本体: GF(3) 2×2 矩阵, 81 个, 谱至多 2 个特征值 (离散)
--   投影: 无穷维 Banach 空间算子, 谱可连续
--   丢失: 有限性 (81→∞), 谱离散性 (有限→连续)
--   截断: 离散谱 → 连续谱 (不可逆退化)
--
-- 退化分类:
--   eval₀-degeneration : Degeneration GF3Func Trit (求值退化)
--   eval₀-section      : Section GF3Func Trit      (常数截面)
--   trace-degeneration : Degeneration Mat2x2 Trit   (迹退化)
--   trace-section      : Section Mat2x2 Trit        (标量截面)
--------------------------------------------------------------------------------
